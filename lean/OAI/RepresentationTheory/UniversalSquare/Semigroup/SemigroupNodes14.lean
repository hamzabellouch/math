import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes12
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes11

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6130 : RowSquare [5,4,2,2,2,2,1,1] [4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg2598

lemma sg6131 : RowSquare [5,4,2,2,2,2,1,1] [4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg561 sg838

lemma sg6132 : RowSquare [5,4,2,2,2,2,1,1] [4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg2599

lemma sg6133 : RowSquare [5,4,2,2,2,2,1,1] [4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg2600

lemma sg6134 : RowSquare [5,4,2,2,2,2,1,1] [4,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg2598

lemma sg6135 : RowSquare [5,4,2,2,2,2,1,1] [4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg562 sg838

lemma sg6136 : RowSquare [5,4,2,2,2,2,1,1] [4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg2599

lemma sg6137 : RowSquare [5,4,2,2,2,2,1,1] [5,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg2596

lemma sg6138 : RowSquare [5,4,2,2,2,2,1,1] [5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg2597

lemma sg6139 : RowSquare [5,4,2,2,2,2,1,1] [5,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg2597

lemma sg6140 : RowSquare [5,4,2,2,2,2,1,1] [5,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg2603

lemma sg6141 : RowSquare [5,4,2,2,2,2,1,1] [5,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg2598

lemma sg6142 : RowSquare [5,4,2,2,2,2,1,1] [5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg2603

lemma sg6143 : RowSquare [5,4,2,2,2,2,1,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg2596

lemma sg6144 : RowSquare [5,4,2,2,2,2,1,1] [6,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg2597

lemma sg6145 : RowSquare [5,4,2,2,2,2,1,1] [6,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg2603

lemma sg6146 : RowSquare [5,4,2,2,2,2,1,1] [7,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg2597

lemma sg6147 : RowSquare [5,4,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg1682

lemma sg6148 : RowSquare [5,4,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg849

lemma sg6149 : RowSquare [5,4,3,2,1,1,1,1,1] [3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg1682

lemma sg6150 : RowSquare [5,4,3,2,1,1,1,1,1] [3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg1683

lemma sg6151 : RowSquare [5,4,3,2,1,1,1,1,1] [3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg850

lemma sg6152 : RowSquare [5,4,3,2,1,1,1,1,1] [3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg180 sg1682

lemma sg6153 : RowSquare [5,4,3,2,1,1,1,1,1] [3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg181 sg1682

lemma sg6154 : RowSquare [5,4,3,2,1,1,1,1,1] [3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg1686

lemma sg6155 : RowSquare [5,4,3,2,1,1,1,1,1] [3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg178 sg1688

lemma sg6156 : RowSquare [5,4,3,2,1,1,1,1,1] [4,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg182 sg1682

lemma sg6157 : RowSquare [5,4,3,2,1,1,1,1,1] [4,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg1683

lemma sg6158 : RowSquare [5,4,3,2,1,1,1,1,1] [4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg183 sg1682

lemma sg6159 : RowSquare [5,4,3,2,1,1,1,1,1] [4,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg180 sg1683

lemma sg6160 : RowSquare [5,4,3,2,1,1,1,1,1] [4,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg184 sg1682

lemma sg6161 : RowSquare [5,4,3,2,1,1,1,1,1] [4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg181 sg1683

lemma sg6162 : RowSquare [5,4,3,2,1,1,1,1,1] [4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg179 sg1688

lemma sg6163 : RowSquare [5,4,3,2,1,1,1,1,1] [4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg862

lemma sg6164 : RowSquare [5,4,3,2,1,1,1,1,1] [5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg3299

lemma sg6165 : RowSquare [5,4,3,2,1,1,1,1,1] [5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg868

lemma sg6166 : RowSquare [5,4,3,2,1,1,1,1,1] [5,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg869

lemma sg6167 : RowSquare [5,4,3,2,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg3300

lemma sg6168 : RowSquare [5,4,3,2,1,1,1,1,1] [6,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg3301

lemma sg6169 : RowSquare [5,4,3,2,1,1,1,1,1] [6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg871

lemma sg6170 : RowSquare [5,4,3,2,1,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5298

lemma sg6171 : RowSquare [5,4,3,2,1,1,1,1,1] [7,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg191 sg1682

lemma sg6172 : RowSquare [5,4,3,2,1,1,1,1,1] [7,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg4639

lemma sg6173 : RowSquare [5,4,3,2,1,1,1,1,1] [7,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg4640

lemma sg6174 : RowSquare [5,4,3,2,1,1,1,1,1] [8,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5300

lemma sg6175 : RowSquare [5,4,3,2,1,1,1,1,1] [8,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg4642

lemma sg6176 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg997

lemma sg6177 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg998

lemma sg6178 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1000

lemma sg6179 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1001

lemma sg6180 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg1002

lemma sg6181 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1003

lemma sg6182 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg587 sg998

lemma sg6183 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1004

lemma sg6184 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg587 sg999

lemma sg6185 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1005

lemma sg6186 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1000

lemma sg6187 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1001

lemma sg6188 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1006

lemma sg6189 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg588 sg998

lemma sg6190 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1007

lemma sg6191 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg589 sg998

lemma sg6192 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg999

lemma sg6193 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1008

lemma sg6194 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg998

lemma sg6195 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg588 sg1000

lemma sg6196 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1001

lemma sg6197 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg589 sg999

lemma sg6198 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg590 sg999

lemma sg6199 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg589 sg1000

lemma sg6200 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg589 sg1001

lemma sg6201 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg590 sg1000

lemma sg6202 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg590 sg1001

lemma sg6203 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg587 sg1002

lemma sg6204 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1004

lemma sg6205 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1012

lemma sg6206 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1005

lemma sg6207 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg591 sg1000

lemma sg6208 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg591 sg1001

lemma sg6209 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1013

lemma sg6210 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg1003

lemma sg6211 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1014

lemma sg6212 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1008

lemma sg6213 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1005

lemma sg6214 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg593 sg999

lemma sg6215 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg589 sg1004

lemma sg6216 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg594 sg999

lemma sg6217 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg589 sg1005

lemma sg6218 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg593 sg1001

lemma sg6219 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg594 sg1000

lemma sg6220 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg590 sg1005

lemma sg6221 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1015

lemma sg6222 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg595 sg998

lemma sg6223 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg588 sg1006

lemma sg6224 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1016

lemma sg6225 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg596 sg998

lemma sg6226 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1007

lemma sg6227 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg589 sg1006

lemma sg6228 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1008

lemma sg6229 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg590 sg1006

lemma sg6230 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg595 sg1001

lemma sg6231 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg596 sg999

lemma sg6232 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,5,4,3,2] := by
  exact rowSquare_join (by decide) sg590 sg1007

lemma sg6233 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg590 sg1008

lemma sg6234 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1017

lemma sg6235 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg587 sg1009

lemma sg6236 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1018

lemma sg6237 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1010

lemma sg6238 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg1009

lemma sg6239 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1019

lemma sg6240 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1011

lemma sg6241 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg591 sg1004

lemma sg6242 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1012

lemma sg6243 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg591 sg1005

lemma sg6244 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg597 sg1000

lemma sg6245 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg597 sg1001

lemma sg6246 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1020

lemma sg6247 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1013

lemma sg6248 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg588 sg1010

lemma sg6249 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1021

lemma sg6250 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1014

lemma sg6251 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1011

lemma sg6252 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg589 sg1010

lemma sg6253 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1012

lemma sg6254 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg592 sg1005

lemma sg6255 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,4,3,3,3] := by
  exact rowSquare_join (by decide) sg598 sg1001

lemma sg6256 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg599 sg999

lemma sg6257 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg589 sg1011

lemma sg6258 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg589 sg1012

lemma sg6259 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,4,4,3,2] := by
  exact rowSquare_join (by decide) sg590 sg1011

lemma sg6260 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,4,4,4,1] := by
  exact rowSquare_join (by decide) sg590 sg1012

lemma sg6261 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1022

lemma sg6262 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1015

lemma sg6263 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1013

lemma sg6264 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg592 sg1006

lemma sg6265 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1016

lemma sg6266 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1014

lemma sg6267 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg589 sg1013

lemma sg6268 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg592 sg1008

lemma sg6269 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,5,3,3,2] := by
  exact rowSquare_join (by decide) sg590 sg1013

lemma sg6270 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg601 sg999

lemma sg6271 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg589 sg1014

lemma sg6272 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,5,4,2,2] := by
  exact rowSquare_join (by decide) sg593 sg1007

lemma sg6273 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,5,4,3,1] := by
  exact rowSquare_join (by decide) sg590 sg1014

lemma sg6274 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,5,4,4] := by
  exact rowSquare_join (by decide) sg594 sg1008

lemma sg6275 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1023

lemma sg6276 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg602 sg998

lemma sg6277 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1015

lemma sg6278 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg595 sg1006

lemma sg6279 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1016

lemma sg6280 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,6,3,2,1,1] := by
  exact rowSquare_join (by decide) sg589 sg1015

lemma sg6281 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,6,3,2,2] := by
  exact rowSquare_join (by decide) sg595 sg1007

lemma sg6282 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [6,6,3,3,1] := by
  exact rowSquare_join (by decide) sg590 sg1015

lemma sg6283 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg4643

lemma sg6284 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [7,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1026

lemma sg6285 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [7,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg4647

lemma sg6286 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [7,7,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1023

lemma sg6287 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [7,7,2,2,1] := by
  exact rowSquare_join (by decide) sg590 sg1023

lemma sg6288 : RowSquare [5,5,2,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg910

lemma sg6289 : RowSquare [5,5,2,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg587 sg910

lemma sg6290 : RowSquare [5,5,2,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg911

lemma sg6291 : RowSquare [5,5,2,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg910

lemma sg6292 : RowSquare [5,5,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg915

lemma sg6293 : RowSquare [5,5,2,1,1,1,1,1,1,1] [4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg589 sg914

lemma sg6294 : RowSquare [5,5,2,1,1,1,1,1,1,1] [6,6,6,1] := by
  exact rowSquare_join (by decide) sg13 sg3173

lemma sg6295 : RowSquare [5,5,2,2,1,1,1,1,1] [3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg534 sg910

lemma sg6296 : RowSquare [5,5,2,2,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg910

lemma sg6297 : RowSquare [5,5,2,2,1,1,1,1,1] [3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg838

lemma sg6298 : RowSquare [5,5,2,2,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg910

lemma sg6299 : RowSquare [5,5,2,2,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg910

lemma sg6300 : RowSquare [5,5,2,2,1,1,1,1,1] [3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg840

lemma sg6301 : RowSquare [5,5,2,2,1,1,1,1,1] [3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg841

lemma sg6302 : RowSquare [5,5,2,2,1,1,1,1,1] [4,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg538 sg910

lemma sg6303 : RowSquare [5,5,2,2,1,1,1,1,1] [4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg842

lemma sg6304 : RowSquare [5,5,2,2,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg539 sg910

lemma sg6305 : RowSquare [5,5,2,2,1,1,1,1,1] [4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg587 sg838

lemma sg6306 : RowSquare [5,5,2,2,1,1,1,1,1] [4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg844

lemma sg6307 : RowSquare [5,5,2,2,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg540 sg910

lemma sg6308 : RowSquare [5,5,2,2,1,1,1,1,1] [4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg845

lemma sg6309 : RowSquare [5,5,2,2,1,1,1,1,1] [4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg587 sg840

lemma sg6310 : RowSquare [5,5,2,2,1,1,1,1,1] [4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg841

lemma sg6311 : RowSquare [5,5,2,2,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg541 sg910

lemma sg6312 : RowSquare [5,5,2,2,1,1,1,1,1] [4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg846

lemma sg6313 : RowSquare [5,5,2,2,1,1,1,1,1] [4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg588 sg838

lemma sg6314 : RowSquare [5,5,2,2,1,1,1,1,1] [4,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg542 sg910

lemma sg6315 : RowSquare [5,5,2,2,1,1,1,1,1] [4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg543 sg910

lemma sg6316 : RowSquare [5,5,2,2,1,1,1,1,1] [4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg847

lemma sg6317 : RowSquare [5,5,2,2,2,2,1] [4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg3998

lemma sg6318 : RowSquare [5,5,2,2,2,2,1] [5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg3999

lemma sg6319 : RowSquare [5,5,2,2,2,2,1] [5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg4002

lemma sg6320 : RowSquare [5,5,2,2,2,2,1] [5,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg4003

lemma sg6321 : RowSquare [5,5,2,2,2,2,1] [5,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6 sg4004

lemma sg6322 : RowSquare [5,5,2,2,2,2,1] [5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6 sg4005

lemma sg6323 : RowSquare [5,5,2,2,2,2,1] [5,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg4007

lemma sg6324 : RowSquare [5,5,2,2,2,2,1] [5,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg4009

lemma sg6325 : RowSquare [5,5,2,2,2,2,1] [5,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg4010

lemma sg6326 : RowSquare [5,5,2,2,2,2,1] [5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg4011

lemma sg6327 : RowSquare [5,5,2,2,2,2,1] [5,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg4015

lemma sg6328 : RowSquare [5,5,2,2,2,2,1] [5,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg4016

lemma sg6329 : RowSquare [5,5,2,2,2,2,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg4006

lemma sg6330 : RowSquare [5,5,2,2,2,2,1] [6,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg4018

lemma sg6331 : RowSquare [5,5,2,2,2,2,1] [6,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg4009

lemma sg6332 : RowSquare [5,5,2,2,2,2,1] [6,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg4010

lemma sg6333 : RowSquare [5,5,2,2,2,2,1] [6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6 sg4011

lemma sg6334 : RowSquare [5,5,2,2,2,2,1] [6,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg4019

lemma sg6335 : RowSquare [5,5,2,2,2,2,1] [6,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg4020

lemma sg6336 : RowSquare [5,5,2,2,2,2,1] [6,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4022

lemma sg6337 : RowSquare [5,5,2,2,2,2,1] [7,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg4018

lemma sg6338 : RowSquare [5,5,2,2,2,2,1] [7,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg4019

lemma sg6340 : RowSquare [6,4,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg1327

lemma sg6341 : RowSquare [6,4,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg372 sg1327

lemma sg6342 : RowSquare [6,4,1,1,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg1327

lemma sg6343 : RowSquare [6,4,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg370 sg1329

lemma sg6344 : RowSquare [6,4,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg370 sg1330

lemma sg6345 : RowSquare [6,4,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg1329

lemma sg6346 : RowSquare [6,4,1,1,1,1,1,1,1,1,1] [4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg1331

lemma sg6347 : RowSquare [6,4,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg374 sg1328

lemma sg6348 : RowSquare [6,4,1,1,1,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg383 sg1327

lemma sg6349 : RowSquare [6,4,2,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg1754

lemma sg6350 : RowSquare [6,4,2,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1327

lemma sg6351 : RowSquare [6,4,2,1,1,1,1,1,1,1] [3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg1754

lemma sg6352 : RowSquare [6,4,2,1,1,1,1,1,1,1] [3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg180 sg1754

lemma sg6353 : RowSquare [6,4,2,1,1,1,1,1,1,1] [4,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg182 sg1754

lemma sg6354 : RowSquare [6,4,2,1,1,1,1,1,1,1] [4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg183 sg1754

lemma sg6355 : RowSquare [6,4,2,1,1,1,1,1,1,1] [4,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg184 sg1754

lemma sg6356 : RowSquare [6,4,2,1,1,1,1,1,1,1] [4,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg185 sg1754

lemma sg6357 : RowSquare [6,4,2,1,1,1,1,1,1,1] [5,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg186 sg1754

lemma sg6358 : RowSquare [6,4,2,1,1,1,1,1,1,1] [5,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg187 sg1754

lemma sg6359 : RowSquare [6,4,2,1,1,1,1,1,1,1] [5,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg188 sg1754

lemma sg6360 : RowSquare [6,4,2,1,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg342 sg1327

lemma sg6361 : RowSquare [6,4,2,1,1,1,1,1,1,1] [6,6,6,1] := by
  exact rowSquare_join (by decide) sg4 sg3848

lemma sg6362 : RowSquare [6,4,2,1,1,1,1,1,1,1] [7,6,6] := by
  exact rowSquare_join (by decide) sg16 sg3173

lemma sg6363 : RowSquare [6,4,2,1,1,1,1,1,1,1] [8,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg4728

lemma sg6364 : RowSquare [6,4,2,2,1,1,1,1,1] [3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg142 sg1754

lemma sg6365 : RowSquare [6,4,2,2,1,1,1,1,1] [3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5507

lemma sg6366 : RowSquare [6,4,2,2,1,1,1,1,1] [3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg143 sg1754

lemma sg6367 : RowSquare [6,4,2,2,1,1,1,1,1] [3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg295 sg1327

lemma sg6368 : RowSquare [6,4,2,2,1,1,1,1,1] [3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg144 sg1754

lemma sg6369 : RowSquare [6,4,2,2,1,1,1,1,1] [4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg4063

lemma sg6370 : RowSquare [6,4,2,2,1,1,1,1,1] [4,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg148 sg1754

lemma sg6371 : RowSquare [6,4,2,2,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg143 sg1755

lemma sg6372 : RowSquare [6,4,2,2,1,1,1,1,1] [4,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg144 sg1755

lemma sg6373 : RowSquare [6,4,2,2,1,1,1,1,1] [4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg295 sg1332

lemma sg6374 : RowSquare [6,4,2,2,1,1,1,1,1] [5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg4064

lemma sg6375 : RowSquare [6,4,2,2,1,1,1,1,1] [5,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg4065

lemma sg6376 : RowSquare [6,4,2,2,1,1,1,1,1] [5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg4066

lemma sg6377 : RowSquare [6,4,2,2,1,1,1,1,1] [5,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg148 sg1755

lemma sg6378 : RowSquare [6,4,2,2,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5510

lemma sg6379 : RowSquare [6,4,2,2,1,1,1,1,1] [6,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg4071

lemma sg6380 : RowSquare [6,4,2,2,1,1,1,1,1] [6,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg4729

lemma sg6381 : RowSquare [6,4,2,2,1,1,1,1,1] [6,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg303 sg1327

lemma sg6382 : RowSquare [6,4,2,2,1,1,1,1,1] [6,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg4730

lemma sg6383 : RowSquare [6,4,2,2,1,1,1,1,1] [6,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg304 sg1327

lemma sg6384 : RowSquare [6,4,2,2,1,1,1,1,1] [6,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg305 sg1327

lemma sg6385 : RowSquare [6,4,2,2,1,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5511

lemma sg6386 : RowSquare [6,4,2,2,1,1,1,1,1] [7,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg4731

lemma sg6387 : RowSquare [6,4,2,2,1,1,1,1,1] [7,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg4732

lemma sg6388 : RowSquare [6,4,2,2,1,1,1,1,1] [7,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg4733

lemma sg6390 : RowSquare [6,4,4,3,1,1] [2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg560 sg730

lemma sg6391 : RowSquare [6,5,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg312 sg1327

lemma sg6392 : RowSquare [6,5,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg5525

lemma sg6393 : RowSquare [6,5,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg313 sg1327

lemma sg6394 : RowSquare [6,5,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg889

lemma sg6395 : RowSquare [6,5,1,1,1,1,1,1,1,1] [3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg314 sg1327

lemma sg6396 : RowSquare [6,5,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg890

lemma sg6397 : RowSquare [6,5,1,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg1327

lemma sg6398 : RowSquare [6,5,1,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg892

lemma sg6399 : RowSquare [6,5,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg312 sg1328

lemma sg6400 : RowSquare [6,5,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg5526

lemma sg6401 : RowSquare [6,5,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg587 sg889

lemma sg6402 : RowSquare [6,5,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg588 sg889

lemma sg6403 : RowSquare [6,5,1,1,1,1,1,1,1,1] [4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg313 sg1332

lemma sg6404 : RowSquare [6,5,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg589 sg890

lemma sg6405 : RowSquare [6,5,1,1,1,1,1,1,1,1] [4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg589 sg891

lemma sg6406 : RowSquare [6,5,2,1,1,1,1,1,1] [3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg270 sg1327

lemma sg6407 : RowSquare [6,5,2,1,1,1,1,1,1] [3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg807

lemma sg6408 : RowSquare [6,5,2,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg1327

lemma sg6409 : RowSquare [6,5,2,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg808

lemma sg6410 : RowSquare [6,5,2,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg809

lemma sg6411 : RowSquare [6,5,2,1,1,1,1,1,1] [4,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg132 sg1754

lemma sg6412 : RowSquare [6,5,2,1,1,1,1,1,1] [4,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg272 sg1327

lemma sg6413 : RowSquare [6,5,2,1,1,1,1,1,1] [4,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg4776

lemma sg6414 : RowSquare [6,5,2,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg4777

lemma sg6415 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg133 sg1754

lemma sg6416 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg273 sg1327

lemma sg6417 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5601

lemma sg6418 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg534 sg889

lemma sg6419 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg134 sg1754

lemma sg6420 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg274 sg1327

lemma sg6421 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5602

lemma sg6422 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5603

lemma sg6423 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg3911

lemma sg6424 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5604

lemma sg6425 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg587 sg808

lemma sg6426 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg809

lemma sg6427 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg275 sg1327

lemma sg6428 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg814

lemma sg6429 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg535 sg889

lemma sg6430 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg276 sg1327

lemma sg6431 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg815

lemma sg6432 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3912

lemma sg6433 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg816

lemma sg6434 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg889

lemma sg6435 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg817

lemma sg6436 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3913

lemma sg6437 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3914

lemma sg6438 : RowSquare [6,5,2,1,1,1,1,1,1] [5,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg135 sg1754

lemma sg6439 : RowSquare [6,5,2,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg4778

lemma sg6440 : RowSquare [6,5,2,1,1,1,1,1,1] [5,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg136 sg1754

lemma sg6441 : RowSquare [6,5,2,1,1,1,1,1,1] [5,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg4780

lemma sg6442 : RowSquare [6,5,2,1,1,1,1,1,1] [5,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg4781

lemma sg6443 : RowSquare [6,5,2,1,1,1,1,1,1] [5,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg137 sg1754

lemma sg6444 : RowSquare [6,5,2,1,1,1,1,1,1] [5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg280 sg1327

lemma sg6445 : RowSquare [6,5,2,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg281 sg1327

lemma sg6446 : RowSquare [6,5,2,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg822

lemma sg6447 : RowSquare [6,5,2,1,1,1,1,1,1] [5,5,5,4] := by
  exact rowSquare_join (by decide) sg13 sg3197

lemma sg6448 : RowSquare [6,5,2,1,1,1,1,1,1] [6,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg138 sg1754

lemma sg6449 : RowSquare [6,5,2,1,1,1,1,1,1] [6,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg282 sg1327

lemma sg6450 : RowSquare [6,5,2,1,1,1,1,1,1] [6,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg139 sg1754

lemma sg6451 : RowSquare [6,5,2,1,1,1,1,1,1] [6,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg283 sg1327

lemma sg6452 : RowSquare [6,5,2,1,1,1,1,1,1] [6,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg284 sg1327

lemma sg6453 : RowSquare [6,5,2,2,2,1,1] [5,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5698

lemma sg6454 : RowSquare [6,5,2,2,2,1,1] [5,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5699

lemma sg6455 : RowSquare [6,5,2,2,2,1,1] [5,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5700

lemma sg6456 : RowSquare [6,5,2,2,2,1,1] [5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg5701

lemma sg6458 : RowSquare [6,5,3,2,2,1] [2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg507 sg757

lemma sg6459 : RowSquare [6,5,3,2,2,1] [3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg496 sg756

lemma sg6460 : RowSquare [6,5,3,2,2,1] [4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg2036

lemma sg6461 : RowSquare [6,5,3,2,2,1] [8,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg466 sg793

lemma sg6462 : RowSquare [6,5,3,2,2,1] [8,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg467 sg793

lemma sg6463 : RowSquare [6,5,3,2,2,1] [8,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg468 sg793

lemma sg6464 : RowSquare [6,6,1,1,1,1,1,1,1] [4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3210

lemma sg6465 : RowSquare [6,6,1,1,1,1,1,1,1] [5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg260 sg1327

lemma sg6466 : RowSquare [6,6,1,1,1,1,1,1,1] [5,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg261 sg1327

lemma sg6467 : RowSquare [6,6,1,1,1,1,1,1,1] [5,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg262 sg1327

lemma sg6468 : RowSquare [7,4,3,2,1,1,1] [2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg632 sg729

lemma sg6469 : RowSquare [7,4,3,2,1,1,1] [2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg632 sg728

lemma sg6470 : RowSquare [7,4,3,2,1,1,1] [2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg632 sg727

lemma sg6471 : RowSquare [7,4,3,2,1,1,1] [2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg560 sg748

lemma sg6472 : RowSquare [7,5,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3964

lemma sg6473 : RowSquare [7,5,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg3964

lemma sg6474 : RowSquare [7,5,1,1,1,1,1,1,1] [4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3965

lemma sg6475 : RowSquare [7,5,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg3966

lemma sg6476 : RowSquare [7,5,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3255

lemma sg6477 : RowSquare [7,5,1,1,1,1,1,1,1] [4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3257

lemma sg6478 : RowSquare [7,5,1,1,1,1,1,1,1] [5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg51 sg2251

lemma sg6479 : RowSquare [7,5,1,1,1,1,1,1,1] [5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg4845

lemma sg6480 : RowSquare [7,5,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6 sg3964

lemma sg6481 : RowSquare [7,5,1,1,1,1,1,1,1] [5,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg52 sg2251

lemma sg6482 : RowSquare [7,5,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg3966

lemma sg6483 : RowSquare [7,5,1,1,1,1,1,1,1] [6,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg53 sg2251

lemma sg6484 : RowSquare [7,5,1,1,1,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg54 sg2251

lemma sg6485 : RowSquare [7,5,2,1,1,1,1,1] [3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg32 sg2546

lemma sg6486 : RowSquare [8,3,2,2,2,1,1] [3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg32 sg2546

lemma sg6487 : RowSquare [8,3,3,1,1,1,1,1] [2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg642 sg734

lemma sg6488 : RowSquare [8,3,3,1,1,1,1,1] [3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg220 sg1586

lemma sg6489 : RowSquare [8,3,3,1,1,1,1,1] [4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg89 sg2038

lemma sg6490 : RowSquare [8,4,4,3] [4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg551 sg834

lemma sg6491 : RowSquare [9,3,3,2,1,1] [5,5,5,4] := by
  exact rowSquare_join (by decide) sg373 sg1200

lemma sg6492 : RowSquare [9,4,3,1,1,1] [2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg306 sg1327

lemma sg6493 : RowSquare [9,4,3,1,1,1] [3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg306 sg1330

lemma sg6494 : RowSquare [9,4,3,1,1,1] [3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg306 sg1331

lemma sg6495 : RowSquare [9,4,3,1,1,1] [4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg390 sg1196

lemma sg6496 : RowSquare [9,4,3,1,1,1] [5,5,5,4] := by
  exact rowSquare_join (by decide) sg390 sg1200

lemma sg6497 : RowSquare [9,4,3,2,1] [2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg849

lemma sg6498 : RowSquare [9,4,3,2,1] [3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg178 sg1688

lemma sg6499 : RowSquare [9,4,3,2,1] [4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg179 sg1688

lemma sg6500 : RowSquare [9,4,4,1,1] [3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg516 sg1001

lemma sg6501 : RowSquare [9,5,3,1,1] [4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg577 sg912

lemma sg6503 : RowSquare [10,3,2,1,1,1,1] [2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg2251

lemma sg6504 : RowSquare [10,3,2,2,1,1] [2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg1754

lemma sg6505 : RowSquare [10,3,2,2,1,1] [4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg332 sg1332

lemma sg6506 : RowSquare [10,3,2,2,1,1] [4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg615 sg891

lemma sg6507 : RowSquare [10,3,2,2,1,1] [4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg334 sg1331

lemma sg6508 : RowSquare [10,3,2,2,2] [4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg913

lemma sg6509 : RowSquare [10,3,3,1,1,1] [4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg348 sg1332

lemma sg6510 : RowSquare [10,3,3,1,1,1] [4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg350 sg1330

lemma sg6511 : RowSquare [10,3,3,1,1,1] [4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg350 sg1331

lemma sg6512 : RowSquare [10,3,3,1,1,1] [4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg637 sg891

lemma sg6513 : RowSquare [10,3,3,2,1] [4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg550 sg1000

lemma sg6514 : RowSquare [10,3,3,2,1] [4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg550 sg1001

lemma sg6515 : RowSquare [10,3,3,2,1] [4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg551 sg1001

lemma sg6516 : RowSquare [10,3,3,2,1] [5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg552 sg1001

lemma sg6517 : RowSquare [10,3,3,2,1] [5,5,5,4] := by
  exact rowSquare_join (by decide) sg373 sg1272

lemma sg6518 : RowSquare [10,4,2,1,1,1] [3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg358 sg1327

lemma sg6519 : RowSquare [10,4,2,1,1,1] [4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg358 sg1329

lemma sg6520 : RowSquare [3,2,2,2,2,2,1,1,1,1,1,1,1] [7,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1068 sg1115

lemma sg6521 : RowSquare [3,2,2,2,2,2,1,1,1,1,1,1,1] [7,6,4,2,1] := by
  exact rowSquare_join (by decide) sg1069 sg1115

lemma sg6522 : RowSquare [3,2,2,2,2,2,1,1,1,1,1,1,1] [7,6,4,3] := by
  exact rowSquare_join (by decide) sg693 sg1549

lemma sg6523 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [6,5,5,2,2] := by
  exact rowSquare_join (by decide) sg1061 sg1114

lemma sg6524 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [6,5,5,3,1] := by
  exact rowSquare_join (by decide) sg692 sg1539

lemma sg6525 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [6,5,5,4] := by
  exact rowSquare_join (by decide) sg693 sg1539

lemma sg6526 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [6,6,4,2,2] := by
  exact rowSquare_join (by decide) sg1061 sg1115

lemma sg6527 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [6,6,4,3,1] := by
  exact rowSquare_join (by decide) sg694 sg1539

lemma sg6528 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [6,6,4,4] := by
  exact rowSquare_join (by decide) sg390 sg1980

lemma sg6529 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [6,6,5,2,1] := by
  exact rowSquare_join (by decide) sg695 sg1538

lemma sg6530 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [6,6,5,3] := by
  exact rowSquare_join (by decide) sg695 sg1539

lemma sg6531 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1068 sg1104

lemma sg6532 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1068 sg1105

lemma sg6533 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1061 sg1116

end UniversalTensorSquare
end
end

end OAI
