import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes15
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes16

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10138 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5130

lemma sg10139 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg74 sg3777

lemma sg10140 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1230

lemma sg10141 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg55 sg3836

lemma sg10142 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,4,3,3] := by
  exact rowSquare_join (by decide) sg40 sg4571

lemma sg10143 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg74 sg3781

lemma sg10144 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg27 sg4622

lemma sg10145 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg55 sg3837

lemma sg10146 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg3782

lemma sg10147 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg74 sg3783

lemma sg10148 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,5,3,2] := by
  exact rowSquare_join (by decide) sg76 sg3766

lemma sg10149 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,5,4,1] := by
  exact rowSquare_join (by decide) sg76 sg3767

lemma sg10150 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,5,5] := by
  exact rowSquare_join (by decide) sg76 sg3768

lemma sg10151 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg55 sg3838

lemma sg10152 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg3784

lemma sg10153 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,6,2,2] := by
  exact rowSquare_join (by decide) sg77 sg3766

lemma sg10154 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,6,3,1] := by
  exact rowSquare_join (by decide) sg77 sg3767

lemma sg10155 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,6,4] := by
  exact rowSquare_join (by decide) sg77 sg3768

lemma sg10156 : RowSquare [6,5,3,2,1,1,1,1,1,1] [7,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg3785

lemma sg10157 : RowSquare [6,5,3,2,1,1,1,1,1,1] [7,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg55 sg3843

lemma sg10158 : RowSquare [6,5,3,2,1,1,1,1,1,1] [7,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg165 sg3160

lemma sg10159 : RowSquare [6,5,3,2,1,1,1,1,1,1] [7,6,6,2,1] := by
  exact rowSquare_join (by decide) sg167 sg3157

lemma sg10160 : RowSquare [6,5,3,2,1,1,1,1,1,1] [7,6,6,3] := by
  exact rowSquare_join (by decide) sg167 sg3158

lemma sg10161 : RowSquare [6,5,3,2,1,1,1,1,1,1] [7,7,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5133

lemma sg10162 : RowSquare [6,5,3,2,1,1,1,1,1,1] [7,7,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg3786

lemma sg10163 : RowSquare [6,5,3,2,1,1,1,1,1,1] [7,7,3,3,1,1] := by
  exact rowSquare_join (by decide) sg74 sg3787

lemma sg10164 : RowSquare [6,5,3,2,1,1,1,1,1,1] [7,7,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg55 sg3847

lemma sg10165 : RowSquare [6,5,3,2,1,1,1,1,1,1] [7,7,4,2,2] := by
  exact rowSquare_join (by decide) sg166 sg3159

lemma sg10166 : RowSquare [6,5,3,2,1,1,1,1,1,1] [7,7,4,4] := by
  exact rowSquare_join (by decide) sg76 sg3781

lemma sg10167 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1327 sg1327

lemma sg10168 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1327 sg1328

lemma sg10169 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1329

lemma sg10170 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1330

lemma sg10171 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1331

lemma sg10172 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1332

lemma sg10173 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1333

lemma sg10174 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1328 sg1328

lemma sg10175 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1334

lemma sg10176 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1328 sg1329

lemma sg10177 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1335

lemma sg10178 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1330

lemma sg10179 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1336

lemma sg10180 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1331

lemma sg10181 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1337

lemma sg10182 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1332

lemma sg10183 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1338

lemma sg10184 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1329 sg1329

lemma sg10185 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1339

lemma sg10186 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1329 sg1330

lemma sg10187 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1340

lemma sg10188 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1331

lemma sg10189 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1332

lemma sg10190 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1330 sg1330

lemma sg10191 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1330 sg1331

lemma sg10192 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1332

lemma sg10193 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1331 sg1331

lemma sg10194 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1331 sg1332

lemma sg10195 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg1332 sg1332

lemma sg10196 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1341

lemma sg10197 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1328 sg1333

lemma sg10198 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1342

lemma sg10199 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1334

lemma sg10200 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1329 sg1333

lemma sg10201 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1343

lemma sg10202 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1335

lemma sg10203 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1333 sg1330

lemma sg10204 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1344

lemma sg10205 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1336

lemma sg10206 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1333 sg1331

lemma sg10207 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1337

lemma sg10208 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1333 sg1332

lemma sg10209 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1345

lemma sg10210 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1338

lemma sg10211 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1329 sg1334

lemma sg10212 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1346

lemma sg10213 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1339

lemma sg10214 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1335

lemma sg10215 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1330 sg1334

lemma sg10216 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1347

lemma sg10217 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1340

lemma sg10218 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1336

lemma sg10219 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1334 sg1331

lemma sg10220 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1337

lemma sg10221 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1334 sg1332

lemma sg10222 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1330 sg1335

lemma sg10223 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1336

lemma sg10224 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1331 sg1335

lemma sg10225 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1337

lemma sg10226 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1335 sg1332

lemma sg10227 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1331 sg1336

lemma sg10228 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1337

lemma sg10229 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1336

lemma sg10230 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1332 sg1337

lemma sg10231 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1348

lemma sg10232 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1338

lemma sg10233 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,5,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1349

lemma sg10234 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1339

lemma sg10235 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1330 sg1338

lemma sg10236 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1340

lemma sg10237 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1331 sg1338

lemma sg10238 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1338 sg1332

lemma sg10239 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1339

lemma sg10240 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1340

lemma sg10241 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1331 sg1339

lemma sg10242 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1339

lemma sg10243 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1340

lemma sg10244 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1332 sg1340

lemma sg10245 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1350

lemma sg10246 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1341

lemma sg10247 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6905

lemma sg10248 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1351

lemma sg10249 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1342

lemma sg10250 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6906

lemma sg10251 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1352

lemma sg10252 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1343

lemma sg10253 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6907

lemma sg10254 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1330 sg1341

lemma sg10255 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1353

lemma sg10256 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1344

lemma sg10257 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6908

lemma sg10258 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1341 sg1331

lemma sg10259 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6909

lemma sg10260 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1341 sg1332

lemma sg10261 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1354

lemma sg10262 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1345

lemma sg10263 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1342

lemma sg10264 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6910

lemma sg10265 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1355

lemma sg10266 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1346

lemma sg10267 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1343

lemma sg10268 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6911

lemma sg10269 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1347

lemma sg10270 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1344

lemma sg10271 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6912

lemma sg10272 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1331 sg1342

lemma sg10273 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6913

lemma sg10274 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1342 sg1332

lemma sg10275 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1343

lemma sg10276 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6914

lemma sg10277 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1344

lemma sg10278 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6915

lemma sg10279 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6916

lemma sg10280 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1343

lemma sg10281 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1344

lemma sg10282 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6917

lemma sg10283 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1 sg6918

lemma sg10284 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1 sg6919

lemma sg10285 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1356

lemma sg10286 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1348

lemma sg10287 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1345

lemma sg10288 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1334 sg1338

lemma sg10289 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1357

lemma sg10290 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1349

lemma sg10291 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1346

lemma sg10292 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1345

lemma sg10293 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1335 sg1338

lemma sg10294 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1347

lemma sg10295 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1334 sg1340

lemma sg10296 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1331 sg1345

lemma sg10297 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1338 sg1337

lemma sg10298 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1345

lemma sg10299 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1346

lemma sg10300 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1335 sg1339

lemma sg10301 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1347

lemma sg10302 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1346

lemma sg10303 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1336 sg1339

lemma sg10304 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1332 sg1346

lemma sg10305 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1347

lemma sg10306 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1332 sg1347

lemma sg10307 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg1337 sg1340

lemma sg10308 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,6,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1358

lemma sg10309 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1348

lemma sg10310 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1338 sg1338

lemma sg10311 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1349

lemma sg10312 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1348

lemma sg10313 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1338 sg1339

lemma sg10314 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1348

lemma sg10315 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1332 sg1348

lemma sg10316 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1349

lemma sg10317 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1339 sg1339

lemma sg10318 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1349

lemma sg10319 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1332 sg1349

lemma sg10320 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,2] := by
  exact rowSquare_join (by decide) sg1340 sg1340

lemma sg10321 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1359

lemma sg10322 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1350

lemma sg10323 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6920

lemma sg10324 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1360

lemma sg10325 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1351

lemma sg10326 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6921

lemma sg10327 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6922

lemma sg10328 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1361

lemma sg10329 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1352

lemma sg10330 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6923

lemma sg10331 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6924

lemma sg10332 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1353

lemma sg10333 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6925

lemma sg10334 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6926

lemma sg10335 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg5135

lemma sg10336 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6927

lemma sg10337 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1350 sg1332

lemma sg10338 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1362

lemma sg10339 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1354

lemma sg10340 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6928

lemma sg10341 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6929

lemma sg10342 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1363

lemma sg10343 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1355

lemma sg10344 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6930

lemma sg10345 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6931

lemma sg10346 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6932

lemma sg10347 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6933

lemma sg10348 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6934

lemma sg10349 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5136

lemma sg10350 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6936

lemma sg10351 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1351

lemma sg10352 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1352

lemma sg10353 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6937

lemma sg10354 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1353

lemma sg10355 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5137

lemma sg10356 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6939

lemma sg10357 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg6940

lemma sg10358 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5138

lemma sg10359 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6941

lemma sg10360 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1 sg6942

lemma sg10361 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1364

lemma sg10362 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1356

lemma sg10363 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1354

lemma sg10364 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6943

lemma sg10365 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1338 sg1342

lemma sg10366 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1357

lemma sg10367 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1355

lemma sg10368 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6944

lemma sg10369 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6945

lemma sg10370 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6946

lemma sg10371 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1354

lemma sg10372 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg5139

lemma sg10373 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg6948

lemma sg10374 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1355

lemma sg10375 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6949

lemma sg10376 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1339 sg1343

lemma sg10377 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6950

lemma sg10378 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5140

lemma sg10379 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,4,3,3] := by
  exact rowSquare_join (by decide) sg1 sg6952

lemma sg10380 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5141

lemma sg10381 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,2] := by
  exact rowSquare_join (by decide) sg1 sg6954

lemma sg10382 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,5,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5142

lemma sg10383 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,5,4,1] := by
  exact rowSquare_join (by decide) sg13 sg5143

lemma sg10384 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,5,5] := by
  exact rowSquare_join (by decide) sg13 sg5144

lemma sg10385 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1365

lemma sg10386 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1358

lemma sg10387 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1356

lemma sg10388 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1334 sg1348

lemma sg10389 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1338 sg1345

lemma sg10390 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1357

lemma sg10391 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1356

lemma sg10392 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1335 sg1348

lemma sg10393 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1339 sg1345

lemma sg10394 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1356

lemma sg10395 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1332 sg1356

lemma sg10396 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,3] := by
  exact rowSquare_join (by decide) sg1337 sg1348

lemma sg10397 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1357

lemma sg10398 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1357

lemma sg10399 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1332 sg1357

lemma sg10400 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1336 sg1349

lemma sg10401 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,2] := by
  exact rowSquare_join (by decide) sg1337 sg1349

lemma sg10402 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,1] := by
  exact rowSquare_join (by decide) sg1340 sg1347

lemma sg10403 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1358

lemma sg10404 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,7,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1338 sg1348

lemma sg10405 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,7,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1358

lemma sg10406 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,7,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1358

lemma sg10407 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,7,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1332 sg1358

lemma sg10408 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,2] := by
  exact rowSquare_join (by decide) sg1340 sg1348

lemma sg10409 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,7,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1339 sg1349

lemma sg10410 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,7,4,3,1] := by
  exact rowSquare_join (by decide) sg1340 sg1349

lemma sg10411 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1366

lemma sg10412 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1359

lemma sg10413 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6955

lemma sg10414 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6956

lemma sg10415 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1367

lemma sg10416 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1360

lemma sg10417 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6957

lemma sg10418 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6958

lemma sg10419 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1368

lemma sg10420 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1361

lemma sg10421 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6959

lemma sg10422 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6960

lemma sg10423 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6961

lemma sg10424 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6962

lemma sg10425 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6963

lemma sg10426 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5145

lemma sg10427 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6964

lemma sg10428 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1359

lemma sg10429 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1369

lemma sg10430 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1362

lemma sg10431 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6965

lemma sg10432 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6966

lemma sg10433 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg5135

lemma sg10434 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1363

lemma sg10435 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6968

lemma sg10436 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6969

lemma sg10437 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6970

lemma sg10438 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6971

lemma sg10439 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5146

lemma sg10440 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg5147

lemma sg10441 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg6973

lemma sg10442 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1361

lemma sg10443 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6974

lemma sg10444 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6975

lemma sg10445 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5148

lemma sg10446 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5149

lemma sg10447 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,3] := by
  exact rowSquare_join (by decide) sg1 sg6978

lemma sg10448 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5150

lemma sg10449 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,2] := by
  exact rowSquare_join (by decide) sg1 sg6980

lemma sg10450 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1370

lemma sg10451 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1364

lemma sg10452 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6981

lemma sg10453 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6982

lemma sg10454 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg5136

lemma sg10455 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6984

lemma sg10456 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6985

lemma sg10457 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5137

lemma sg10458 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6986

lemma sg10459 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5151

lemma sg10460 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5152

lemma sg10461 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg6988

lemma sg10462 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1363

lemma sg10463 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5153

lemma sg10464 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6990

lemma sg10465 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5154

lemma sg10466 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5155

lemma sg10467 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,1] := by
  exact rowSquare_join (by decide) sg13 sg5156

lemma sg10468 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,5,3,1] := by
  exact rowSquare_join (by decide) sg13 sg5157

lemma sg10469 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,5,4] := by
  exact rowSquare_join (by decide) sg13 sg5158

lemma sg10470 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1365

lemma sg10471 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1364

lemma sg10472 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6994

lemma sg10473 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1338 sg1354

lemma sg10474 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg5139

lemma sg10475 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6996

lemma sg10476 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6997

lemma sg10477 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg5140

lemma sg10478 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5159

lemma sg10479 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg7000

lemma sg10480 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7001

lemma sg10481 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5160

lemma sg10482 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,4,2,2] := by
  exact rowSquare_join (by decide) sg14 sg5142

lemma sg10483 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg5161

lemma sg10484 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,4,4] := by
  exact rowSquare_join (by decide) sg13 sg5162

lemma sg10485 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,5,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5163

lemma sg10486 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,5,3] := by
  exact rowSquare_join (by decide) sg13 sg5164

lemma sg10487 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,7,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1365

lemma sg10488 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,7,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1365

lemma sg10489 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,7,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1365

lemma sg10490 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,7,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1332 sg1365

lemma sg10491 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,7,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1335 sg1358

lemma sg10492 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,7,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1336 sg1358

lemma sg10493 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,7,3,2,2] := by
  exact rowSquare_join (by decide) sg1337 sg1358

lemma sg10494 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,7,3,3,1] := by
  exact rowSquare_join (by decide) sg1340 sg1356

lemma sg10495 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,7,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1339 sg1357

lemma sg10496 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,7,4,2,1] := by
  exact rowSquare_join (by decide) sg1340 sg1357

lemma sg10497 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,7,4,3] := by
  exact rowSquare_join (by decide) sg1347 sg1349

lemma sg10498 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,8,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1338 sg1358

lemma sg10499 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,8,2,2,2] := by
  exact rowSquare_join (by decide) sg1348 sg1348

lemma sg10500 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,8,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1339 sg1358

lemma sg10501 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,8,3,2,1] := by
  exact rowSquare_join (by decide) sg1340 sg1358

lemma sg10502 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,8,4,2] := by
  exact rowSquare_join (by decide) sg1349 sg1349

lemma sg10503 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7004

lemma sg10504 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg5165

lemma sg10505 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg7005

lemma sg10506 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7006

lemma sg10507 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg7007

lemma sg10508 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5166

lemma sg10509 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,4,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg7008

lemma sg10510 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg7009

lemma sg10511 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5167

lemma sg10512 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,4,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5168

lemma sg10513 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,1] := by
  exact rowSquare_join (by decide) sg13 sg5169

lemma sg10514 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7010

lemma sg10515 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg5147

lemma sg10516 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7011

lemma sg10517 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg5149

lemma sg10518 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5170

lemma sg10519 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,5,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5171

lemma sg10520 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5172

lemma sg10521 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,5,4,2,2] := by
  exact rowSquare_join (by decide) sg1 sg7012

lemma sg10522 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,5,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg5173

lemma sg10523 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,5,4,4] := by
  exact rowSquare_join (by decide) sg13 sg5174

lemma sg10524 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,5,5,3] := by
  exact rowSquare_join (by decide) sg13 sg5175

lemma sg10525 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg5152

lemma sg10526 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,6,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5176

lemma sg10527 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,6,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg5155

lemma sg10528 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,6,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg5177

lemma sg10529 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7015

lemma sg10530 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,6,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5178

lemma sg10531 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,6,4,3] := by
  exact rowSquare_join (by decide) sg13 sg5179

lemma sg10532 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg7016

lemma sg10533 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,7,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5180

lemma sg10534 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,7,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg7017

lemma sg10535 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,7,3,3] := by
  exact rowSquare_join (by decide) sg13 sg5181

lemma sg10536 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,8,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1339 sg1365

lemma sg10537 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,8,2,2,1] := by
  exact rowSquare_join (by decide) sg1340 sg1365

end UniversalTensorSquare
end
end

end OAI
