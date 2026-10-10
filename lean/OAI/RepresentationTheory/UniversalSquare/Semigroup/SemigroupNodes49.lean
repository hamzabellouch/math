import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes32
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes37
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes21

namespace OAI

/-! Semigroup Nodes 49. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20140 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,6,4,3] := by
  exact rowSquare_join (by decide) sg365 sg11099

lemma sg20141 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,6,5,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11130

lemma sg20142 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,6,5,2] := by
  exact rowSquare_join (by decide) sg364 sg11131

lemma sg20143 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,6,6,1] := by
  exact rowSquare_join (by decide) sg364 sg11132

lemma sg20144 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,9,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg208 sg11674

lemma sg20145 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,9,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg14 sg14391

lemma sg20146 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,9,3,3,3,3] := by
  exact rowSquare_join (by decide) sg715 sg11050

lemma sg20147 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,9,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg209 sg11674

lemma sg20148 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,9,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg207 sg11708

lemma sg20149 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,9,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg210 sg11656

lemma sg20150 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,9,4,3,3,2] := by
  exact rowSquare_join (by decide) sg14 sg14392

lemma sg20151 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,9,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11133

lemma sg20152 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,9,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11134

lemma sg20153 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,9,4,4,2,2] := by
  exact rowSquare_join (by decide) sg364 sg11135

lemma sg20154 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,9,4,4,3,1] := by
  exact rowSquare_join (by decide) sg208 sg11680

lemma sg20155 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,9,4,4,4] := by
  exact rowSquare_join (by decide) sg213 sg11615

lemma sg20156 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14393

lemma sg20157 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg14394

lemma sg20158 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg12909

lemma sg20159 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg210 sg11673

lemma sg20160 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg210 sg11674

lemma sg20161 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14402

lemma sg20162 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14403

lemma sg20163 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14404

lemma sg20164 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14396

lemma sg20165 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,3,3,3,2] := by
  exact rowSquare_join (by decide) sg14 sg14397

lemma sg20166 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12586

lemma sg20167 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg11675

lemma sg20168 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg210 sg11676

lemma sg20169 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg11709

lemma sg20170 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg365 sg11106

lemma sg20171 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,4,3,2,2] := by
  exact rowSquare_join (by decide) sg207 sg11710

lemma sg20172 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,4,3,3,1] := by
  exact rowSquare_join (by decide) sg210 sg11680

lemma sg20173 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11136

lemma sg20174 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,4,4,2,1] := by
  exact rowSquare_join (by decide) sg364 sg11137

lemma sg20175 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,4,4,3] := by
  exact rowSquare_join (by decide) sg365 sg11107

lemma sg20176 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,3,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg277 sg11202

lemma sg20177 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg272 sg11217

lemma sg20178 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,3,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3670 sg4051

lemma sg20179 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg278 sg11202

lemma sg20180 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg273 sg11217

lemma sg20181 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg491 sg8940

lemma sg20182 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg272 sg11219

lemma sg20183 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg838 sg8105

lemma sg20184 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg279 sg11202

lemma sg20185 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg274 sg11217

lemma sg20186 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg492 sg8940

lemma sg20187 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg270 sg11235

lemma sg20188 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg489 sg8957

lemma sg20189 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg489 sg8958

lemma sg20190 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg839 sg8105

lemma sg20191 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg493 sg8940

lemma sg20192 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg271 sg11235

lemma sg20193 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg490 sg8957

lemma sg20194 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg490 sg8958

lemma sg20195 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg272 sg11221

lemma sg20196 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg840 sg8105

lemma sg20197 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg277 sg11206

lemma sg20198 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg272 sg11222

lemma sg20199 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg841 sg8105

lemma sg20200 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15220

lemma sg20201 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg280 sg11202

lemma sg20202 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg275 sg11217

lemma sg20203 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg494 sg8940

lemma sg20204 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg273 sg11219

lemma sg20205 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg491 sg8941

lemma sg20206 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg838 sg8106

lemma sg20207 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3275 sg4516

lemma sg20208 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg276 sg11217

lemma sg20209 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg495 sg8940

lemma sg20210 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg274 sg11219

lemma sg20211 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg489 sg8959

lemma sg20212 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg838 sg8107

lemma sg20213 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg489 sg8960

lemma sg20214 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg839 sg8106

lemma sg20215 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg491 sg8945

lemma sg20216 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg838 sg8108

lemma sg20217 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg490 sg8959

lemma sg20218 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg490 sg8960

lemma sg20219 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg490 sg8961

lemma sg20220 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg840 sg8106

lemma sg20221 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg273 sg11222

lemma sg20222 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg841 sg8106

lemma sg20223 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg3284 sg4513

lemma sg20224 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg496 sg8940

lemma sg20225 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg209 sg11694

lemma sg20226 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg489 sg8962

lemma sg20227 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg274 sg11220

lemma sg20228 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg492 sg8943

lemma sg20229 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg489 sg8963

lemma sg20230 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg839 sg8107

lemma sg20231 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg489 sg8964

lemma sg20232 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg490 sg8962

lemma sg20233 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg489 sg8965

lemma sg20234 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg839 sg8108

lemma sg20235 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg490 sg8963

lemma sg20236 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg840 sg8107

lemma sg20237 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg489 sg8966

lemma sg20238 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg841 sg8107

lemma sg20239 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg489 sg8967

lemma sg20240 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg493 sg8945

lemma sg20241 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg490 sg8965

lemma sg20242 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg840 sg8108

lemma sg20243 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg841 sg8108

lemma sg20244 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,5,3,2] := by
  exact rowSquare_join (by decide) sg490 sg8966

lemma sg20245 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg490 sg8967

lemma sg20246 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,5,5,5,5] := by
  exact rowSquare_join (by decide) sg277 sg11216

lemma sg20247 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg281 sg11202

lemma sg20248 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg280 sg11203

lemma sg20249 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg275 sg11218

lemma sg20250 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg275 sg11219

lemma sg20251 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg494 sg8941

lemma sg20252 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg494 sg8942

lemma sg20253 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8109

lemma sg20254 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15221

lemma sg20255 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg276 sg11218

lemma sg20256 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg276 sg11219

lemma sg20257 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg489 sg8968

lemma sg20258 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg495 sg8942

lemma sg20259 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg494 sg8943

lemma sg20260 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8110

lemma sg20261 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg494 sg8944

lemma sg20262 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg839 sg8109

lemma sg20263 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg490 sg8968

lemma sg20264 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8111

lemma sg20265 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg271 sg11236

lemma sg20266 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg490 sg8969

lemma sg20267 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg490 sg8970

lemma sg20268 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,4,3,3] := by
  exact rowSquare_join (by decide) sg840 sg8109

lemma sg20269 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg494 sg8947

lemma sg20270 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,4,4,2] := by
  exact rowSquare_join (by decide) sg841 sg8109

lemma sg20271 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg489 sg8971

lemma sg20272 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg496 sg8942

lemma sg20273 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg490 sg8971

lemma sg20274 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg489 sg8972

lemma sg20275 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg495 sg8944

lemma sg20276 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8112

lemma sg20277 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg839 sg8110

lemma sg20278 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,3,3,3] := by
  exact rowSquare_join (by decide) sg489 sg8974

lemma sg20279 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg495 sg8945

lemma sg20280 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8113

lemma sg20281 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg839 sg8111

lemma sg20282 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg490 sg8973

lemma sg20283 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,4,3,2] := by
  exact rowSquare_join (by decide) sg840 sg8110

lemma sg20284 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,4,4,1] := by
  exact rowSquare_join (by decide) sg841 sg8110

lemma sg20285 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8114

lemma sg20286 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg490 sg8975

lemma sg20287 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,5,2,2] := by
  exact rowSquare_join (by decide) sg840 sg8111

lemma sg20288 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,5,3,1] := by
  exact rowSquare_join (by decide) sg841 sg8111

lemma sg20289 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,5,5,4] := by
  exact rowSquare_join (by decide) sg490 sg8976

lemma sg20290 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg496 sg8943

lemma sg20291 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg496 sg8944

lemma sg20292 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg496 sg8945

lemma sg20293 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg489 sg8977

lemma sg20294 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg839 sg8112

lemma sg20295 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,6,3,3,2] := by
  exact rowSquare_join (by decide) sg489 sg8978

lemma sg20296 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg839 sg8113

lemma sg20297 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,6,4,2,2] := by
  exact rowSquare_join (by decide) sg489 sg8979

lemma sg20298 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,6,4,3,1] := by
  exact rowSquare_join (by decide) sg840 sg8112

lemma sg20299 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,6,4,4] := by
  exact rowSquare_join (by decide) sg841 sg8112

lemma sg20300 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg839 sg8114

lemma sg20301 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,6,5,2,1] := by
  exact rowSquare_join (by decide) sg840 sg8113

lemma sg20302 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,6,5,3] := by
  exact rowSquare_join (by decide) sg841 sg8113

lemma sg20303 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,6,6,1,1] := by
  exact rowSquare_join (by decide) sg840 sg8114

lemma sg20304 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,6,6,2] := by
  exact rowSquare_join (by decide) sg841 sg8114

lemma sg20305 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,7,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg14399

lemma sg20306 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,7,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15222

lemma sg20307 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,7,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg275 sg11223

lemma sg20308 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,7,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg494 sg8948

lemma sg20309 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,7,4,3,3,3] := by
  exact rowSquare_join (by decide) sg489 sg8980

lemma sg20310 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,7,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg364 sg11138

lemma sg20311 : RowSquare [8,7,2,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg12954

lemma sg20312 : RowSquare [8,7,2,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg43 sg12955

lemma sg20313 : RowSquare [8,7,2,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg43 sg12956

lemma sg20314 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2251 sg5737

lemma sg20315 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2251 sg5738

lemma sg20316 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5739

lemma sg20317 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5740

lemma sg20318 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5741

lemma sg20319 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2252 sg5740

lemma sg20320 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2252 sg5741

lemma sg20321 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3523 sg4165

lemma sg20322 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5742

lemma sg20323 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3524 sg4165

lemma sg20324 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5743

lemma sg20325 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3524 sg4167

lemma sg20326 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5746

lemma sg20327 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2256 sg5738

lemma sg20328 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15628

lemma sg20329 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg2256 sg5745

lemma sg20330 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15629

lemma sg20331 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14417

lemma sg20332 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14418

lemma sg20333 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,2,1] := by
  exact rowSquare_join (by decide) sg4 sg14756

lemma sg20334 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,3] := by
  exact rowSquare_join (by decide) sg4 sg14757

lemma sg20335 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14419

lemma sg20336 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14420

lemma sg20337 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,3] := by
  exact rowSquare_join (by decide) sg13 sg14421

lemma sg20338 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14422

lemma sg20339 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,2] := by
  exact rowSquare_join (by decide) sg13 sg14423

lemma sg20340 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,6,1] := by
  exact rowSquare_join (by decide) sg32 sg13506

lemma sg20341 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,6,5,5,5,3] := by
  exact rowSquare_join (by decide) sg5 sg14757

lemma sg20342 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,6,6,5,5,2] := by
  exact rowSquare_join (by decide) sg4 sg14758

lemma sg20343 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14425

lemma sg20344 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,6] := by
  exact rowSquare_join (by decide) sg32 sg13507

lemma sg20345 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg14 sg14418

lemma sg20346 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg14427

lemma sg20347 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14422

lemma sg20348 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,5,2] := by
  exact rowSquare_join (by decide) sg14 sg14423

lemma sg20349 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,6,4,4,3] := by
  exact rowSquare_join (by decide) sg4 sg14759

lemma sg20350 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14428

lemma sg20351 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14429

lemma sg20352 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14430

lemma sg20353 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14431

lemma sg20354 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,2] := by
  exact rowSquare_join (by decide) sg13 sg14432

lemma sg20355 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,4,1] := by
  exact rowSquare_join (by decide) sg13 sg14433

lemma sg20356 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,5] := by
  exact rowSquare_join (by decide) sg13 sg14434

lemma sg20357 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12589

lemma sg20358 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,7,5,5] := by
  exact rowSquare_join (by decide) sg83 sg12590

lemma sg20359 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,7,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14435

lemma sg20360 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,7,6,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14436

lemma sg20361 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,7,7,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14437

lemma sg20362 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,7,7,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14438

lemma sg20363 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,7,7,3] := by
  exact rowSquare_join (by decide) sg13 sg14439

lemma sg20364 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg15227

lemma sg20365 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15228

lemma sg20366 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15631

lemma sg20367 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg0 sg15632

lemma sg20368 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14440

lemma sg20369 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15633

lemma sg20370 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg14760

lemma sg20371 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg14441

lemma sg20372 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg6 sg14757

lemma sg20373 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15634

lemma sg20374 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2260 sg5748

lemma sg20375 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2265 sg5747

lemma sg20376 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg14442

lemma sg20377 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,6,5,5,5,2] := by
  exact rowSquare_join (by decide) sg5 sg14758

lemma sg20378 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,3,2] := by
  exact rowSquare_join (by decide) sg165 sg11719

lemma sg20379 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,6,6,4,4,3] := by
  exact rowSquare_join (by decide) sg4 sg14761

lemma sg20380 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,6,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12589

lemma sg20381 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3531 sg4169

lemma sg20382 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg165 sg11720

lemma sg20383 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,7,5,4,4,3] := by
  exact rowSquare_join (by decide) sg14 sg14424

lemma sg20384 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg165 sg11721

lemma sg20385 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,7,7,7,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12914

lemma sg20386 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,7,7,7,2] := by
  exact rowSquare_join (by decide) sg39 sg12915

lemma sg20387 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3532 sg4169

lemma sg20388 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg74 sg12592

lemma sg20389 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14443

lemma sg20390 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg14 sg14426

lemma sg20391 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,3] := by
  exact rowSquare_join (by decide) sg14 sg14427

lemma sg20392 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,8,7,7,1] := by
  exact rowSquare_join (by decide) sg13 sg14444

lemma sg20393 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,8,8,6,1] := by
  exact rowSquare_join (by decide) sg207 sg11712

lemma sg20394 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,8,8,7] := by
  exact rowSquare_join (by decide) sg207 sg11713

lemma sg20395 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg3537 sg4156

lemma sg20396 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg14762

lemma sg20397 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg14445

lemma sg20398 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg15 sg14423

lemma sg20399 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,6,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg14441

lemma sg20400 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg356 sg11140

lemma sg20401 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg4 sg14763

lemma sg20402 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg165 sg11722

lemma sg20403 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,7,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15635

lemma sg20404 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,7,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg356 sg11143

lemma sg20405 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg14 sg14442

lemma sg20406 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,7,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg356 sg11145

lemma sg20407 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,7,6,3,3,3] := by
  exact rowSquare_join (by decide) sg165 sg11723

lemma sg20408 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,8,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg356 sg11146

lemma sg20409 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,8,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg356 sg11147

lemma sg20410 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg356 sg11148

lemma sg20411 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,9,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg207 sg11714

lemma sg20412 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [9,9,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg356 sg11149

lemma sg20413 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [10,5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg15 sg14424

lemma sg20414 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [10,6,4,4,4,3] := by
  exact rowSquare_join (by decide) sg14 sg14445

lemma sg20415 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [11,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg561 sg8911

lemma sg20416 : RowSquare [8,7,3,3,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2119 sg5737

lemma sg20417 : RowSquare [8,7,3,3,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1663 sg6487

lemma sg20418 : RowSquare [8,7,3,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5669

lemma sg20419 : RowSquare [8,7,3,3,2,1,1,1,1,1,1,1,1] [5,5,5,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1667 sg6487

lemma sg20420 : RowSquare [8,7,3,3,2,1,1,1,1,1,1,1,1] [6,6,6,5,4,4] := by
  exact rowSquare_join (by decide) sg74 sg12719

lemma sg20421 : RowSquare [8,7,3,3,2,1,1,1,1,1,1,1,1] [7,6,6,4,4,4] := by
  exact rowSquare_join (by decide) sg1667 sg6489

lemma sg20422 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3259 sg4347

lemma sg20423 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3260 sg4347

lemma sg20424 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3260 sg4348

lemma sg20425 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [5,5,5,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3264 sg4347

lemma sg20426 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3264 sg4349

lemma sg20427 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg3264 sg4350

lemma sg20428 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3265 sg4349

lemma sg20429 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15238

lemma sg20430 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,5,5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3264 sg4351

lemma sg20431 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,5,5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg3377 sg4025

lemma sg20432 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,5,5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3376 sg4026

lemma sg20433 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,5,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3377 sg4026

lemma sg20434 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,5,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3525 sg3985

lemma sg20435 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,5,5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3376 sg4027

lemma sg20436 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,5,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg3377 sg4027

lemma sg20437 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3523 sg3986

lemma sg20438 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,6,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg3263 sg4354

lemma sg20439 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,6,5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3264 sg4354

lemma sg20440 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,6,5,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14448

lemma sg20441 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,6,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3265 sg4353

lemma sg20442 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14449

lemma sg20443 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,6,6,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3525 sg3987

lemma sg20444 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,6,6,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14550

lemma sg20445 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,6,6,6,3,3,1] := by
  exact rowSquare_join (by decide) sg364 sg11162

lemma sg20446 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,6,6,6,4,3] := by
  exact rowSquare_join (by decide) sg13 sg14450

lemma sg20447 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [6,6,6,6,5,2] := by
  exact rowSquare_join (by decide) sg13 sg14451

lemma sg20448 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,5,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3268 sg4351

lemma sg20449 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,5,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg3377 sg4028

lemma sg20450 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,5,5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3377 sg4029

lemma sg20451 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,5,5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg3378 sg4025

lemma sg20452 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,5,5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg3378 sg4026

lemma sg20453 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,6,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3377 sg4030

lemma sg20454 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,6,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg74 sg12710

lemma sg20455 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,6,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg193 sg12331

lemma sg20456 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,6,5,5,4,4] := by
  exact rowSquare_join (by decide) sg74 sg12711

lemma sg20457 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,6,5,5,5,3] := by
  exact rowSquare_join (by decide) sg74 sg12712

lemma sg20458 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,6,6,4,4,4] := by
  exact rowSquare_join (by decide) sg74 sg12713

lemma sg20459 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,6,6,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg14452

lemma sg20460 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,6,6,5,5,2] := by
  exact rowSquare_join (by decide) sg3379 sg4027

lemma sg20461 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,6,6,6,6] := by
  exact rowSquare_join (by decide) sg792 sg8213

lemma sg20462 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,7,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14453

lemma sg20463 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,7,5,4,4,4] := by
  exact rowSquare_join (by decide) sg74 sg12714

lemma sg20464 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,7,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg364 sg11163

lemma sg20465 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,7,5,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg14454

lemma sg20466 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,7,5,5,5,2] := by
  exact rowSquare_join (by decide) sg14 sg14451

lemma sg20467 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,7,6,4,4,3] := by
  exact rowSquare_join (by decide) sg74 sg12715

lemma sg20468 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,7,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14455

lemma sg20469 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,7,6,6,2,2,1] := by
  exact rowSquare_join (by decide) sg364 sg11164

lemma sg20470 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,7,6,6,3,2] := by
  exact rowSquare_join (by decide) sg580 sg8919

lemma sg20471 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,7,6,6,4,1] := by
  exact rowSquare_join (by decide) sg580 sg8920

lemma sg20472 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,7,6,6,5] := by
  exact rowSquare_join (by decide) sg166 sg11730

lemma sg20473 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,7,7,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3270 sg4347

lemma sg20474 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,7,7,5,5] := by
  exact rowSquare_join (by decide) sg83 sg12593

lemma sg20475 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,7,7,7,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11165

lemma sg20476 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,7,7,7,2,1] := by
  exact rowSquare_join (by decide) sg580 sg8921

lemma sg20477 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [7,7,7,7,3] := by
  exact rowSquare_join (by decide) sg580 sg8922

lemma sg20478 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [8,3,3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15239

lemma sg20479 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [8,4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3269 sg4351

lemma sg20480 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [8,4,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1 sg15240

lemma sg20481 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [8,5,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15241

lemma sg20482 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [8,5,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg3263 sg4357

lemma sg20483 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [8,5,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3378 sg4029

lemma sg20484 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [8,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg74 sg12716

lemma sg20485 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [8,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg74 sg12717

lemma sg20486 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [8,6,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3378 sg4030

lemma sg20487 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [8,6,5,4,4,4] := by
  exact rowSquare_join (by decide) sg193 sg12332

lemma sg20488 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [8,6,5,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg14456

lemma sg20489 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [8,6,5,5,5,2] := by
  exact rowSquare_join (by decide) sg3380 sg4027

lemma sg20490 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [8,7,4,4,4,4] := by
  exact rowSquare_join (by decide) sg74 sg12718

lemma sg20491 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [8,7,5,4,4,3] := by
  exact rowSquare_join (by decide) sg14 sg14452

lemma sg20492 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [9,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg391 sg11536

lemma sg20493 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [9,6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1 sg15242

lemma sg20494 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [10,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1 sg15243

lemma sg20495 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [11,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1 sg15244

lemma sg20496 : RowSquare [9,7,2,2,1,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2156 sg5761

lemma sg20497 : RowSquare [9,7,2,2,1,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2156 sg5762

lemma sg20498 : RowSquare [9,7,2,2,2,2,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4846

lemma sg20499 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4834

lemma sg20500 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4835

lemma sg20501 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4836

lemma sg20502 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2879 sg4776

lemma sg20503 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2879 sg4777

lemma sg20504 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4837

lemma sg20505 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2704 sg4834

lemma sg20506 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4838

lemma sg20507 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2704 sg4835

lemma sg20508 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5661

lemma sg20509 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14766

lemma sg20510 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14767

lemma sg20511 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg14768

lemma sg20512 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14769

lemma sg20513 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg12594

lemma sg20514 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2705 sg4835

lemma sg20515 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5662

lemma sg20516 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14770

lemma sg20517 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2706 sg4834

lemma sg20518 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4840

lemma sg20519 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg12595

lemma sg20520 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4841

lemma sg20521 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5663

lemma sg20522 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2707 sg4834

lemma sg20523 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4842

lemma sg20524 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2074 sg5759

lemma sg20525 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg4834

lemma sg20526 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2074 sg5760

lemma sg20527 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14771

lemma sg20528 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2880 sg4776

lemma sg20529 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2879 sg4779

lemma sg20530 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2880 sg4777

lemma sg20531 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg14770

lemma sg20532 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2709 sg4834

lemma sg20533 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2075 sg5760

lemma sg20534 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2251 sg5664

lemma sg20535 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2704 sg4837

lemma sg20536 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4843

lemma sg20537 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg12596

lemma sg20538 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1188 sg8000

lemma sg20539 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg14771

end UniversalTensorSquare
end
end

end OAI
