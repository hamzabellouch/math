import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes17
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes20

namespace OAI

/-! Semigroup Nodes 29. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12140 : RowSquare [8,6,2,2,2,2,1,1] [7,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg4632

lemma sg12141 : RowSquare [8,6,2,2,2,2,1,1] [7,5,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg766 sg2583

lemma sg12142 : RowSquare [8,6,2,2,2,2,1,1] [7,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2050

lemma sg12143 : RowSquare [8,6,2,2,2,2,1,1] [7,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1203 sg2047

lemma sg12144 : RowSquare [8,6,2,2,2,2,1,1] [7,5,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg767 sg2583

lemma sg12145 : RowSquare [8,6,2,2,2,2,1,1] [7,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2051

lemma sg12146 : RowSquare [8,6,2,2,2,2,1,1] [7,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1203 sg2048

lemma sg12147 : RowSquare [8,6,2,2,2,2,1,1] [7,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1203 sg2049

lemma sg12148 : RowSquare [8,6,2,2,2,2,1,1] [7,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2052

lemma sg12149 : RowSquare [8,6,2,2,2,2,1,1] [7,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1210 sg2044

lemma sg12150 : RowSquare [8,6,2,2,2,2,1,1] [7,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg4627

lemma sg12151 : RowSquare [8,6,2,2,2,2,1,1] [7,5,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg768 sg2583

lemma sg12152 : RowSquare [8,6,2,2,2,2,1,1] [7,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg810 sg2560

lemma sg12153 : RowSquare [8,6,2,2,2,2,1,1] [7,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1203 sg2050

lemma sg12154 : RowSquare [8,6,2,2,2,2,1,1] [7,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg810 sg2561

lemma sg12155 : RowSquare [8,6,2,2,2,2,1,1] [7,6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7275

lemma sg12156 : RowSquare [8,6,2,2,2,2,1,1] [7,6,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg6141

lemma sg12157 : RowSquare [8,6,2,2,2,2,1,1] [7,6,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg7477

lemma sg12158 : RowSquare [8,6,2,2,2,2,1,1] [7,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7276

lemma sg12159 : RowSquare [8,6,2,2,2,2,1,1] [7,6,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg765 sg2585

lemma sg12160 : RowSquare [8,6,2,2,2,2,1,1] [7,6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1202 sg2053

lemma sg12161 : RowSquare [8,6,2,2,2,2,1,1] [7,6,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg6142

lemma sg12162 : RowSquare [8,6,2,2,2,2,1,1] [7,6,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg4633

lemma sg12163 : RowSquare [8,6,2,2,2,2,1,1] [7,6,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg766 sg2585

lemma sg12164 : RowSquare [8,6,2,2,2,2,1,1] [7,6,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2054

lemma sg12165 : RowSquare [8,6,2,2,2,2,1,1] [7,6,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1203 sg2053

lemma sg12166 : RowSquare [8,6,2,2,2,2,1,1] [7,6,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg767 sg2585

lemma sg12167 : RowSquare [8,6,2,2,2,2,1,1] [7,6,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2055

lemma sg12168 : RowSquare [8,6,2,2,2,2,1,1] [7,6,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1206 sg2048

lemma sg12169 : RowSquare [8,6,2,2,2,2,1,1] [7,6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg4628

lemma sg12170 : RowSquare [8,6,2,2,2,2,1,1] [7,6,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg768 sg2585

lemma sg12171 : RowSquare [8,6,2,2,2,2,1,1] [7,6,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2056

lemma sg12172 : RowSquare [8,6,2,2,2,2,1,1] [7,6,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2057

lemma sg12173 : RowSquare [8,6,2,2,2,2,1,1] [7,6,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg773 sg2579

lemma sg12174 : RowSquare [8,6,2,2,2,2,1,1] [7,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2058

lemma sg12175 : RowSquare [8,6,2,2,2,2,1,1] [7,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg459 sg3285

lemma sg12176 : RowSquare [8,6,2,2,2,2,1,1] [7,7,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7277

lemma sg12177 : RowSquare [8,6,2,2,2,2,1,1] [7,7,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7278

lemma sg12178 : RowSquare [8,6,2,2,2,2,1,1] [7,7,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg7478

lemma sg12179 : RowSquare [8,6,2,2,2,2,1,1] [7,7,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg780 sg2576

lemma sg12180 : RowSquare [8,6,2,2,2,2,1,1] [7,7,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg765 sg2586

lemma sg12181 : RowSquare [8,6,2,2,2,2,1,1] [7,7,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1206 sg2053

lemma sg12182 : RowSquare [8,6,2,2,2,2,1,1] [7,7,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg4628

lemma sg12183 : RowSquare [8,6,2,2,2,2,1,1] [7,7,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg774 sg2579

lemma sg12184 : RowSquare [8,6,2,2,2,2,1,1] [7,7,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg766 sg2586

lemma sg12185 : RowSquare [8,6,2,2,2,2,1,1] [7,7,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg767 sg2586

lemma sg12186 : RowSquare [8,6,2,2,2,2,1,1] [7,7,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg775 sg2579

lemma sg12187 : RowSquare [8,6,2,2,2,2,1,1] [7,7,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg768 sg2586

lemma sg12188 : RowSquare [8,6,2,2,2,2,1,1] [7,7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg403 sg3788

lemma sg12189 : RowSquare [8,6,2,2,2,2,1,1] [8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg8691

lemma sg12190 : RowSquare [8,6,2,2,2,2,1,1] [8,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg7269

lemma sg12191 : RowSquare [8,6,2,2,2,2,1,1] [8,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7279

lemma sg12192 : RowSquare [8,6,2,2,2,2,1,1] [8,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6143

lemma sg12193 : RowSquare [8,6,2,2,2,2,1,1] [8,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg8692

lemma sg12194 : RowSquare [8,6,2,2,2,2,1,1] [8,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg8693

lemma sg12195 : RowSquare [8,6,2,2,2,2,1,1] [8,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg8694

lemma sg12196 : RowSquare [8,6,2,2,2,2,1,1] [8,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6 sg8695

lemma sg12197 : RowSquare [8,6,2,2,2,2,1,1] [8,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6 sg8696

lemma sg12198 : RowSquare [8,6,2,2,2,2,1,1] [8,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7279

lemma sg12199 : RowSquare [8,6,2,2,2,2,1,1] [8,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg6143

lemma sg12200 : RowSquare [8,6,2,2,2,2,1,1] [8,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6144

lemma sg12201 : RowSquare [8,6,2,2,2,2,1,1] [8,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg8703

lemma sg12202 : RowSquare [8,6,2,2,2,2,1,1] [8,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg8704

lemma sg12203 : RowSquare [8,6,2,2,2,2,1,1] [8,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg8705

lemma sg12204 : RowSquare [8,6,2,2,2,2,1,1] [8,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg8706

lemma sg12205 : RowSquare [8,6,2,2,2,2,1,1] [8,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg6138

lemma sg12206 : RowSquare [8,6,2,2,2,2,1,1] [8,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg98 sg5287

lemma sg12207 : RowSquare [8,6,2,2,2,2,1,1] [8,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7280

lemma sg12208 : RowSquare [8,6,2,2,2,2,1,1] [8,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7281

lemma sg12209 : RowSquare [8,6,2,2,2,2,1,1] [8,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7282

lemma sg12210 : RowSquare [8,6,2,2,2,2,1,1] [8,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg100 sg5281

lemma sg12211 : RowSquare [8,6,2,2,2,2,1,1] [8,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg98 sg5288

lemma sg12212 : RowSquare [8,6,2,2,2,2,1,1] [8,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg7479

lemma sg12213 : RowSquare [8,6,2,2,2,2,1,1] [8,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg776 sg2577

lemma sg12214 : RowSquare [8,6,2,2,2,2,1,1] [8,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1209 sg2045

lemma sg12215 : RowSquare [8,6,2,2,2,2,1,1] [8,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1678 sg1592

lemma sg12216 : RowSquare [8,6,2,2,2,2,1,1] [8,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1209 sg2046

lemma sg12217 : RowSquare [8,6,2,2,2,2,1,1] [8,4,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg6137

lemma sg12218 : RowSquare [8,6,2,2,2,2,1,1] [8,4,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg6144

lemma sg12219 : RowSquare [8,6,2,2,2,2,1,1] [8,4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg98 sg5289

lemma sg12220 : RowSquare [8,6,2,2,2,2,1,1] [8,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7280

lemma sg12221 : RowSquare [8,6,2,2,2,2,1,1] [8,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7281

lemma sg12222 : RowSquare [8,6,2,2,2,2,1,1] [8,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7282

lemma sg12223 : RowSquare [8,6,2,2,2,2,1,1] [8,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1202 sg2059

lemma sg12224 : RowSquare [8,6,2,2,2,2,1,1] [8,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg5291

lemma sg12225 : RowSquare [8,6,2,2,2,2,1,1] [8,4,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg98 sg5290

lemma sg12226 : RowSquare [8,6,2,2,2,2,1,1] [8,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7283

lemma sg12227 : RowSquare [8,6,2,2,2,2,1,1] [8,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg763 sg2587

lemma sg12228 : RowSquare [8,6,2,2,2,2,1,1] [8,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1202 sg2060

lemma sg12229 : RowSquare [8,6,2,2,2,2,1,1] [8,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg4631

lemma sg12230 : RowSquare [8,6,2,2,2,2,1,1] [8,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1678 sg1593

lemma sg12231 : RowSquare [8,6,2,2,2,2,1,1] [8,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2061

lemma sg12232 : RowSquare [8,6,2,2,2,2,1,1] [8,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1679 sg1592

lemma sg12233 : RowSquare [8,6,2,2,2,2,1,1] [8,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg239 sg4050

lemma sg12234 : RowSquare [8,6,2,2,2,2,1,1] [8,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg4634

lemma sg12235 : RowSquare [8,6,2,2,2,2,1,1] [8,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1678 sg1594

lemma sg12236 : RowSquare [8,6,2,2,2,2,1,1] [8,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1209 sg2050

lemma sg12237 : RowSquare [8,6,2,2,2,2,1,1] [8,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg770 sg2583

lemma sg12238 : RowSquare [8,6,2,2,2,2,1,1] [8,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1209 sg2051

lemma sg12239 : RowSquare [8,6,2,2,2,2,1,1] [8,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1209 sg2052

lemma sg12240 : RowSquare [8,6,2,2,2,2,1,1] [8,5,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg6139

lemma sg12241 : RowSquare [8,6,2,2,2,2,1,1] [8,5,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg99 sg5289

lemma sg12242 : RowSquare [8,6,2,2,2,2,1,1] [8,5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6145

lemma sg12243 : RowSquare [8,6,2,2,2,2,1,1] [8,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7283

lemma sg12244 : RowSquare [8,6,2,2,2,2,1,1] [8,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg765 sg2587

lemma sg12245 : RowSquare [8,6,2,2,2,2,1,1] [8,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1202 sg2062

lemma sg12246 : RowSquare [8,6,2,2,2,2,1,1] [8,5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg239 sg4052

lemma sg12247 : RowSquare [8,6,2,2,2,2,1,1] [8,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg4635

lemma sg12248 : RowSquare [8,6,2,2,2,2,1,1] [8,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg766 sg2587

lemma sg12249 : RowSquare [8,6,2,2,2,2,1,1] [8,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2063

lemma sg12250 : RowSquare [8,6,2,2,2,2,1,1] [8,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1678 sg1595

lemma sg12251 : RowSquare [8,6,2,2,2,2,1,1] [8,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1679 sg1593

lemma sg12252 : RowSquare [8,6,2,2,2,2,1,1] [8,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg4632

lemma sg12253 : RowSquare [8,6,2,2,2,2,1,1] [8,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1678 sg1596

lemma sg12254 : RowSquare [8,6,2,2,2,2,1,1] [8,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1678 sg1597

lemma sg12255 : RowSquare [8,6,2,2,2,2,1,1] [8,6,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg6141

lemma sg12256 : RowSquare [8,6,2,2,2,2,1,1] [8,6,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg240 sg4052

lemma sg12257 : RowSquare [8,6,2,2,2,2,1,1] [8,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg4633

lemma sg12258 : RowSquare [8,6,2,2,2,2,1,1] [8,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg771 sg2585

lemma sg12259 : RowSquare [8,6,2,2,2,2,1,1] [8,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2064

lemma sg12260 : RowSquare [8,6,2,2,2,2,1,1] [8,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg4633

lemma sg12261 : RowSquare [8,6,2,2,2,2,1,1] [8,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg772 sg2585

lemma sg12262 : RowSquare [8,6,2,2,2,2,1,1] [8,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg773 sg2585

lemma sg12263 : RowSquare [8,6,2,2,2,2,1,1] [8,7,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg241 sg4052

lemma sg12264 : RowSquare [8,6,2,2,2,2,1,1] [8,7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg4633

lemma sg12265 : RowSquare [8,6,2,2,2,2,1,1] [8,7,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg774 sg2585

lemma sg12266 : RowSquare [8,6,2,2,2,2,1,1] [8,7,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg775 sg2585

lemma sg12267 : RowSquare [8,6,2,2,2,2,1,1] [8,8,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7284

lemma sg12268 : RowSquare [8,6,2,2,2,2,1,1] [8,8,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg780 sg2579

lemma sg12269 : RowSquare [8,6,2,2,2,2,1,1] [9,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg7269

lemma sg12270 : RowSquare [8,6,2,2,2,2,1,1] [9,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg7279

lemma sg12271 : RowSquare [8,6,2,2,2,2,1,1] [9,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg6143

lemma sg12272 : RowSquare [8,6,2,2,2,2,1,1] [9,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6146

lemma sg12273 : RowSquare [8,6,2,2,2,2,1,1] [9,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg8703

lemma sg12274 : RowSquare [8,6,2,2,2,2,1,1] [9,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg8704

lemma sg12275 : RowSquare [8,6,2,2,2,2,1,1] [9,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg8705

lemma sg12276 : RowSquare [8,6,2,2,2,2,1,1] [9,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6 sg8706

lemma sg12277 : RowSquare [8,6,2,2,2,2,1,1] [9,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg6143

lemma sg12278 : RowSquare [8,6,2,2,2,2,1,1] [9,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg6146

lemma sg12279 : RowSquare [8,6,2,2,2,2,1,1] [9,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg98 sg5291

lemma sg12280 : RowSquare [8,6,2,2,2,2,1,1] [9,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg7280

lemma sg12281 : RowSquare [8,6,2,2,2,2,1,1] [9,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg7281

lemma sg12282 : RowSquare [8,6,2,2,2,2,1,1] [9,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18 sg7282

lemma sg12283 : RowSquare [8,6,2,2,2,2,1,1] [9,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg5292

lemma sg12284 : RowSquare [8,6,2,2,2,2,1,1] [9,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg242 sg4050

lemma sg12285 : RowSquare [8,6,2,2,2,2,1,1] [9,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7285

lemma sg12286 : RowSquare [8,6,2,2,2,2,1,1] [9,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1678 sg1598

lemma sg12287 : RowSquare [8,6,2,2,2,2,1,1] [9,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg211 sg4631

lemma sg12288 : RowSquare [8,6,2,2,2,2,1,1] [9,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1678 sg1599

lemma sg12289 : RowSquare [8,6,2,2,2,2,1,1] [9,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg6144

lemma sg12290 : RowSquare [8,6,2,2,2,2,1,1] [9,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg99 sg5291

lemma sg12291 : RowSquare [8,6,2,2,2,2,1,1] [9,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg242 sg4052

lemma sg12292 : RowSquare [8,6,2,2,2,2,1,1] [9,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7285

lemma sg12293 : RowSquare [8,6,2,2,2,2,1,1] [9,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1678 sg1600

lemma sg12294 : RowSquare [8,6,2,2,2,2,1,1] [9,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg239 sg4054

lemma sg12295 : RowSquare [8,6,2,2,2,2,1,1] [9,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg4636

lemma sg12296 : RowSquare [8,6,2,2,2,2,1,1] [9,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1678 sg1601

lemma sg12297 : RowSquare [8,6,2,2,2,2,1,1] [9,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1678 sg1602

lemma sg12298 : RowSquare [8,6,2,2,2,2,1,1] [9,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg239 sg4055

lemma sg12299 : RowSquare [8,6,2,2,2,2,1,1] [9,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg101 sg5289

lemma sg12300 : RowSquare [8,6,2,2,2,2,1,1] [9,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg240 sg4054

lemma sg12301 : RowSquare [8,6,2,2,2,2,1,1] [9,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg4635

lemma sg12302 : RowSquare [8,6,2,2,2,2,1,1] [9,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1678 sg1603

lemma sg12303 : RowSquare [8,6,2,2,2,2,1,1] [9,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg239 sg4056

lemma sg12304 : RowSquare [8,6,2,2,2,2,1,1] [9,6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg241 sg4054

lemma sg12305 : RowSquare [8,6,2,2,2,2,1,1] [9,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg240 sg4056

lemma sg12306 : RowSquare [8,6,2,2,2,2,1,1] [9,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg241 sg4056

lemma sg12307 : RowSquare [8,6,2,2,2,2,1,1] [10,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg7279

lemma sg12308 : RowSquare [8,6,2,2,2,2,1,1] [10,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg6143

lemma sg12309 : RowSquare [8,6,2,2,2,2,1,1] [10,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg6146

lemma sg12310 : RowSquare [8,6,2,2,2,2,1,1] [10,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg98 sg5292

lemma sg12311 : RowSquare [8,6,2,2,2,2,1,1] [10,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg7280

lemma sg12312 : RowSquare [8,6,2,2,2,2,1,1] [10,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg7281

lemma sg12313 : RowSquare [8,6,2,2,2,2,1,1] [10,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg6146

lemma sg12314 : RowSquare [8,6,2,2,2,2,1,1] [10,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg99 sg5292

lemma sg12315 : RowSquare [8,6,2,2,2,2,1,1] [10,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg242 sg4054

lemma sg12316 : RowSquare [8,6,2,2,2,2,1,1] [10,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg7285

lemma sg12317 : RowSquare [8,6,2,2,2,2,1,1] [10,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg239 sg4058

lemma sg12318 : RowSquare [8,6,2,2,2,2,1,1] [10,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg242 sg4055

lemma sg12319 : RowSquare [8,6,2,2,2,2,1,1] [10,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg101 sg5291

lemma sg12320 : RowSquare [8,6,2,2,2,2,1,1] [10,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg240 sg4058

lemma sg12321 : RowSquare [8,6,2,2,2,2,1,1] [10,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg242 sg4056

lemma sg12322 : RowSquare [8,6,2,2,2,2,1,1] [10,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg241 sg4058

lemma sg12323 : RowSquare [8,6,2,2,2,2,1,1] [11,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg6143

lemma sg12324 : RowSquare [8,6,2,2,2,2,1,1] [11,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg6146

lemma sg12325 : RowSquare [8,6,2,2,2,2,1,1] [11,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg100 sg5292

lemma sg12326 : RowSquare [8,6,2,2,2,2,1,1] [11,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg242 sg4058

lemma sg12327 : RowSquare [8,6,2,2,2,2,1,1] [11,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg101 sg5292

lemma sg12328 : RowSquare [8,6,2,2,2,2,1,1] [11,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg243 sg4058

lemma sg12329 : RowSquare [8,6,2,2,2,2,1,1] [12,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg50 sg5733

lemma sg12330 : RowSquare [8,6,2,2,2,2,1,1] [12,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg102 sg5292

lemma sg12331 : RowSquare [9,3,2,2,2,2,2,2] [5,5,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg579 sg3209

lemma sg12332 : RowSquare [9,3,2,2,2,2,2,2] [6,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg579 sg3213

lemma sg12333 : RowSquare [10,3,2,2,2,2,2,1] [4,4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg5528

lemma sg12334 : RowSquare [10,3,2,2,2,2,2,1] [5,5,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg74 sg5538

lemma sg12335 : RowSquare [10,3,2,2,2,2,2,1] [5,5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg74 sg5544

lemma sg12336 : RowSquare [10,3,2,2,2,2,2,1] [5,5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg5547

lemma sg12337 : RowSquare [10,3,2,2,2,2,2,1] [6,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg165 sg4748

lemma sg12338 : RowSquare [10,3,2,2,2,2,2,1] [6,6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg356 sg3870

lemma sg12339 : RowSquare [10,4,2,2,2,2,2] [6,6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg295 sg3870

lemma sg12340 : RowSquare [11,3,2,2,2,2,1,1] [6,6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg5398

lemma sg12341 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg1914 sg2432

lemma sg12342 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg1914 sg2433

lemma sg12343 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4] := by
  exact rowSquare_join (by decide) sg1532 sg3103

lemma sg12344 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1455 sg3151

lemma sg12345 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,3,1] := by
  exact rowSquare_join (by decide) sg1915 sg2432

lemma sg12346 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4] := by
  exact rowSquare_join (by decide) sg1916 sg2432

lemma sg12347 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,2,1] := by
  exact rowSquare_join (by decide) sg1915 sg2433

lemma sg12348 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3] := by
  exact rowSquare_join (by decide) sg1916 sg2433

lemma sg12349 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,1] := by
  exact rowSquare_join (by decide) sg1917 sg2432

lemma sg12350 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,2,1] := by
  exact rowSquare_join (by decide) sg1917 sg2433

lemma sg12351 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,3] := by
  exact rowSquare_join (by decide) sg1918 sg2432

lemma sg12352 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,1,1] := by
  exact rowSquare_join (by decide) sg636 sg4543

lemma sg12353 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,2] := by
  exact rowSquare_join (by decide) sg1918 sg2433

lemma sg12354 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,1] := by
  exact rowSquare_join (by decide) sg637 sg4543

lemma sg12355 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg1844 sg2461

lemma sg12356 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1844 sg2462

lemma sg12357 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1914 sg2436

lemma sg12358 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1919 sg2432

lemma sg12359 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg1844 sg2463

lemma sg12360 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1919 sg2433

lemma sg12361 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg1535 sg3102

lemma sg12362 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg1914 sg2438

lemma sg12363 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4] := by
  exact rowSquare_join (by decide) sg1970 sg2343

lemma sg12364 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg1914 sg2439

lemma sg12365 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,3] := by
  exact rowSquare_join (by decide) sg1970 sg2344

lemma sg12366 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1456 sg3151

lemma sg12367 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,3,3,2] := by
  exact rowSquare_join (by decide) sg1914 sg2440

lemma sg12368 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1844 sg2464

lemma sg12369 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1914 sg2441

lemma sg12370 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,4] := by
  exact rowSquare_join (by decide) sg1916 sg2436

lemma sg12371 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1971 sg2341

lemma sg12372 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,2,2] := by
  exact rowSquare_join (by decide) sg1844 sg2465

lemma sg12373 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,3,1] := by
  exact rowSquare_join (by decide) sg1914 sg2442

lemma sg12374 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1456 sg3152

lemma sg12375 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,2,1] := by
  exact rowSquare_join (by decide) sg1914 sg2443

lemma sg12376 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,3] := by
  exact rowSquare_join (by decide) sg1916 sg2438

lemma sg12377 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1915 sg2439

lemma sg12378 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,2] := by
  exact rowSquare_join (by decide) sg1916 sg2439

lemma sg12379 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1455 sg3153

lemma sg12380 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1533 sg3104

lemma sg12381 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1915 sg2440

lemma sg12382 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1920 sg2432

lemma sg12383 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1915 sg2441

lemma sg12384 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,3] := by
  exact rowSquare_join (by decide) sg1916 sg2441

lemma sg12385 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1534 sg3104

lemma sg12386 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,2,2,2] := by
  exact rowSquare_join (by decide) sg1917 sg2440

lemma sg12387 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1973 sg2341

lemma sg12388 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,3,2,1] := by
  exact rowSquare_join (by decide) sg1915 sg2442

lemma sg12389 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,3,3] := by
  exact rowSquare_join (by decide) sg1916 sg2442

lemma sg12390 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,1,1] := by
  exact rowSquare_join (by decide) sg1915 sg2443

lemma sg12391 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,2] := by
  exact rowSquare_join (by decide) sg1916 sg2443

lemma sg12392 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,1] := by
  exact rowSquare_join (by decide) sg1980 sg2330

lemma sg12393 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1919 sg2434

lemma sg12394 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg1844 sg2466

lemma sg12395 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1844 sg2467

lemma sg12396 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1914 sg2446

lemma sg12397 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1844 sg2468

lemma sg12398 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1919 sg2435

lemma sg12399 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1846 sg2461

lemma sg12400 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg1844 sg2469

lemma sg12401 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1922 sg2433

lemma sg12402 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1844 sg2470

lemma sg12403 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1914 sg2447

lemma sg12404 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4] := by
  exact rowSquare_join (by decide) sg1916 sg2446

lemma sg12405 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1919 sg2437

lemma sg12406 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1919 sg2438

lemma sg12407 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg1844 sg2471

lemma sg12408 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1919 sg2439

lemma sg12409 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1970 sg2350

lemma sg12410 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1844 sg2472

lemma sg12411 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1919 sg2440

lemma sg12412 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1846 sg2462

lemma sg12413 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1844 sg2473

lemma sg12414 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1458 sg3152

lemma sg12415 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1846 sg2463

lemma sg12416 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,2,2,2] := by
  exact rowSquare_join (by decide) sg1844 sg2474

lemma sg12417 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1919 sg2443

lemma sg12418 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1456 sg3153

lemma sg12419 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1971 sg2350

lemma sg12420 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1844 sg2475

lemma sg12421 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1972 sg2350

lemma sg12422 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1844 sg2476

lemma sg12423 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1846 sg2464

lemma sg12424 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1537 sg3104

lemma sg12425 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1920 sg2440

lemma sg12426 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1973 sg2350

lemma sg12427 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1915 sg2449

lemma sg12428 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1922 sg2434

lemma sg12429 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1844 sg2477

lemma sg12430 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1735 sg2480

lemma sg12431 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1919 sg2444

lemma sg12432 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1735 sg2481

lemma sg12433 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1919 sg2445

lemma sg12434 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1919 sg2446

lemma sg12435 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1923 sg2433

lemma sg12436 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1735 sg2482

lemma sg12437 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1810 sg2478

lemma sg12438 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1922 sg2435

lemma sg12439 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1735 sg2483

lemma sg12440 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1735 sg2484

lemma sg12441 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1] [5,5,5,5,5] := by
  exact rowSquare_join (by decide) sg1061 sg3658

lemma sg12442 : RowSquare [4,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg1891 sg2451

lemma sg12443 : RowSquare [4,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1891 sg2452

lemma sg12444 : RowSquare [4,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg1926 sg2391

lemma sg12445 : RowSquare [4,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1891 sg2453

lemma sg12446 : RowSquare [4,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1919 sg2405

lemma sg12447 : RowSquare [4,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg1902 sg2439

lemma sg12448 : RowSquare [4,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1520 sg3104

lemma sg12449 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1844 sg2392

lemma sg12450 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1892 sg2339

lemma sg12451 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1] [8,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1923 sg2311

lemma sg12452 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1891 sg2212

lemma sg12453 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1] [5,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1735 sg2390

lemma sg12454 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1] [5,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1519 sg2664

lemma sg12455 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1] [5,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1891 sg2214

lemma sg12456 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1] [5,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1891 sg2215

lemma sg12457 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1] [5,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1891 sg2216

lemma sg12458 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1] [5,5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1735 sg2392

lemma sg12459 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1] [6,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1810 sg2310

lemma sg12460 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1] [6,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1810 sg2311

lemma sg12461 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1] [6,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1736 sg2390

lemma sg12462 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1] [6,4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1300 sg3004

lemma sg12463 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1] [6,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1809 sg2314

lemma sg12464 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1] [6,5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1736 sg2392

lemma sg12465 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1] [6,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg3736

lemma sg12466 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1] [7,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1810 sg2313

lemma sg12467 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1] [7,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1810 sg2314

lemma sg12468 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1] [7,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1736 sg2396

lemma sg12469 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1902 sg2405

lemma sg12470 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1902 sg2406

lemma sg12471 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1902 sg2407

lemma sg12472 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg1518 sg3099

lemma sg12473 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg1518 sg3100

lemma sg12474 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4] := by
  exact rowSquare_join (by decide) sg1519 sg3100

lemma sg12475 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1903 sg2405

lemma sg12476 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1903 sg2406

lemma sg12477 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1417 sg3147

lemma sg12478 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1903 sg2407

lemma sg12479 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1417 sg3148

lemma sg12480 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1417 sg3149

lemma sg12481 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1904 sg2405

lemma sg12482 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1904 sg2406

lemma sg12483 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1904 sg2407

lemma sg12484 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,2,2] := by
  exact rowSquare_join (by decide) sg1905 sg2406

lemma sg12485 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,3,1] := by
  exact rowSquare_join (by decide) sg1905 sg2407

lemma sg12486 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4] := by
  exact rowSquare_join (by decide) sg1033 sg3737

lemma sg12487 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1907 sg2405

lemma sg12488 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,2,2] := by
  exact rowSquare_join (by decide) sg1906 sg2406

lemma sg12489 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1908 sg2405

lemma sg12490 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1902 sg2413

lemma sg12491 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg1902 sg2416

lemma sg12492 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1902 sg2419

lemma sg12493 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,4] := by
  exact rowSquare_join (by decide) sg1519 sg3101

lemma sg12494 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1903 sg2417

lemma sg12495 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1520 sg3101

lemma sg12496 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1908 sg2417

lemma sg12497 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1902 sg2424

lemma sg12498 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1902 sg2425

lemma sg12499 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1902 sg2426

lemma sg12500 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1902 sg2427

lemma sg12501 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1904 sg2424

lemma sg12502 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1904 sg2427

lemma sg12503 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1902 sg2429

lemma sg12504 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1957 sg2338

lemma sg12505 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1961 sg2338

lemma sg12506 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1891 sg2405

lemma sg12507 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1539 sg2925

lemma sg12508 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1891 sg2406

lemma sg12509 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1891 sg2407

lemma sg12510 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg1032 sg3724

lemma sg12511 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg3724

lemma sg12512 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,2] := by
  exact rowSquare_join (by decide) sg1032 sg3725

lemma sg12513 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg1032 sg3726

lemma sg12514 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,5] := by
  exact rowSquare_join (by decide) sg1033 sg3726

lemma sg12515 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1901 sg2390

lemma sg12516 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1034 sg3724

lemma sg12517 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1955 sg2310

lemma sg12518 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1956 sg2310

lemma sg12519 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1903 sg2390

lemma sg12520 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1519 sg3002

lemma sg12521 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg1518 sg3004

lemma sg12522 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1901 sg2395

lemma sg12523 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg4539

lemma sg12524 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg1891 sg2416

lemma sg12525 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,4] := by
  exact rowSquare_join (by decide) sg1519 sg3009

lemma sg12526 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1961 sg2311

lemma sg12527 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1903 sg2394

lemma sg12528 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,3,3,3] := by
  exact rowSquare_join (by decide) sg1521 sg3004

lemma sg12529 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1903 sg2395

lemma sg12530 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1891 sg2419

lemma sg12531 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1416 sg3128

lemma sg12532 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg1908 sg2391

lemma sg12533 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1964 sg2310

lemma sg12534 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1524 sg3002

lemma sg12535 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg1955 sg2314

lemma sg12536 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2406

lemma sg12537 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg2407

lemma sg12538 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1874 sg2408

lemma sg12539 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1874 sg2410

end UniversalTensorSquare
end
end

end OAI
