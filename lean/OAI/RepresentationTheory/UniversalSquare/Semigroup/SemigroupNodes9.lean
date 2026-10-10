import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes7

namespace OAI

/-! Semigroup Nodes 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4114 : RowSquare [6,4,3,1,1,1] [4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg1179

lemma sg4115 : RowSquare [6,4,3,1,1,1] [4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg62 sg807

lemma sg4116 : RowSquare [6,4,3,1,1,1] [5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg1646

lemma sg4117 : RowSquare [6,4,3,1,1,1] [5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg27 sg1198

lemma sg4118 : RowSquare [6,4,3,1,1,1] [5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg155 sg457

lemma sg4119 : RowSquare [6,4,3,2,1] [3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg74 sg758

lemma sg4120 : RowSquare [6,4,3,2,1] [3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg759

lemma sg4121 : RowSquare [6,4,3,2,1] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg75 sg759

lemma sg4122 : RowSquare [6,4,3,2,1] [4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1619

lemma sg4123 : RowSquare [6,4,3,2,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg760

lemma sg4124 : RowSquare [6,4,3,3] [3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg254

lemma sg4125 : RowSquare [6,4,3,3] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg66 sg796

lemma sg4126 : RowSquare [6,4,3,3] [4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg255

lemma sg4127 : RowSquare [6,4,3,3] [4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg143 sg481

lemma sg4128 : RowSquare [6,4,3,3] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg68 sg796

lemma sg4129 : RowSquare [6,4,3,3] [4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg333 sg254

lemma sg4130 : RowSquare [6,4,3,3] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg334 sg254

lemma sg4131 : RowSquare [6,4,3,3] [5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg66 sg797

lemma sg4132 : RowSquare [6,4,3,3] [5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg67 sg797

lemma sg4133 : RowSquare [6,4,3,3] [5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg256

lemma sg4134 : RowSquare [6,4,3,3] [5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg145 sg481

lemma sg4135 : RowSquare [6,4,3,3] [5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg143 sg482

lemma sg4136 : RowSquare [6,4,3,3] [5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg336 sg254

lemma sg4137 : RowSquare [6,4,3,3] [5,4,4,3] := by
  exact rowSquare_join (by decide) sg254 sg337

lemma sg4138 : RowSquare [6,4,3,3] [5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg257

lemma sg4139 : RowSquare [6,4,3,3] [5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg143 sg483

lemma sg4140 : RowSquare [6,4,3,3] [5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg333 sg255

lemma sg4141 : RowSquare [6,4,3,3] [5,5,3,3] := by
  exact rowSquare_join (by decide) sg334 sg255

lemma sg4142 : RowSquare [6,4,3,3] [5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg143 sg484

lemma sg4143 : RowSquare [6,4,3,3] [5,5,4,2] := by
  exact rowSquare_join (by decide) sg254 sg339

lemma sg4144 : RowSquare [6,4,3,3] [6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg258

lemma sg4145 : RowSquare [6,4,3,3] [6,5,3,2] := by
  exact rowSquare_join (by decide) sg254 sg341

lemma sg4146 : RowSquare [6,4,3,3] [6,5,4,1] := by
  exact rowSquare_join (by decide) sg144 sg487

lemma sg4147 : RowSquare [6,4,3,3] [6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg333 sg257

lemma sg4148 : RowSquare [6,4,3,3] [6,6,2,2] := by
  exact rowSquare_join (by decide) sg334 sg257

lemma sg4149 : RowSquare [6,4,3,3] [6,6,3,1] := by
  exact rowSquare_join (by decide) sg255 sg339

lemma sg4150 : RowSquare [6,4,3,3] [6,6,4] := by
  exact rowSquare_join (by decide) sg148 sg484

lemma sg4151 : RowSquare [6,5,1,1,1,1,1] [3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1632

lemma sg4152 : RowSquare [6,5,1,1,1,1,1] [4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2082

lemma sg4153 : RowSquare [6,5,1,1,1,1,1] [4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg1632

lemma sg4154 : RowSquare [6,5,1,1,1,1,1] [4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg1636

lemma sg4155 : RowSquare [7,2,1,1,1,1,1,1,1] [2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2251

lemma sg4156 : RowSquare [7,2,2,1,1,1,1,1] [5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg2710

lemma sg4157 : RowSquare [7,2,2,2,2,1] [3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1632

lemma sg4158 : RowSquare [7,3,1,1,1,1,1,1] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg3309

lemma sg4159 : RowSquare [7,3,1,1,1,1,1,1] [5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg3310

lemma sg4161 : RowSquare [7,3,2,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg400 sg238

lemma sg4162 : RowSquare [7,3,2,1,1,1,1] [2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg399 sg238

lemma sg4163 : RowSquare [7,3,2,1,1,1,1] [2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg396 sg238

lemma sg4164 : RowSquare [7,3,2,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg396 sg237

lemma sg4165 : RowSquare [7,3,2,1,1,1,1] [2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg396 sg236

lemma sg4166 : RowSquare [7,3,2,1,1,1,1] [2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg223 sg434

lemma sg4167 : RowSquare [7,3,2,1,1,1,1] [2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg92 sg748

lemma sg4168 : RowSquare [7,3,2,1,1,1,1] [3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg91 sg748

lemma sg4169 : RowSquare [7,3,2,1,1,1,1] [3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg89 sg748

lemma sg4170 : RowSquare [7,3,2,1,1,1,1] [3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg89 sg747

lemma sg4171 : RowSquare [7,3,2,1,1,1,1] [3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg220 sg432

lemma sg4172 : RowSquare [7,3,2,1,1,1,1] [3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg89 sg746

lemma sg4173 : RowSquare [7,3,2,1,1,1,1] [3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg89 sg741

lemma sg4174 : RowSquare [7,3,2,1,1,1,1] [3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg89 sg739

lemma sg4175 : RowSquare [7,3,2,1,1,1,1] [4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg3314

lemma sg4176 : RowSquare [7,3,2,1,1,1,1] [4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg88 sg747

lemma sg4177 : RowSquare [7,3,2,1,1,1,1] [4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg88 sg741

lemma sg4178 : RowSquare [7,3,2,1,1,1,1] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg1187

lemma sg4179 : RowSquare [7,3,2,1,1,1,1] [4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1188

lemma sg4180 : RowSquare [7,3,2,1,1,1,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg88 sg740

lemma sg4181 : RowSquare [7,3,2,1,1,1,1] [5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1192

lemma sg4182 : RowSquare [7,3,2,1,1,1,1] [5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg799

lemma sg4183 : RowSquare [7,3,2,1,1,1,1] [5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg800

lemma sg4184 : RowSquare [7,3,2,1,1,1,1] [6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg802

lemma sg4185 : RowSquare [7,3,2,2,1,1] [3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg2074

lemma sg4186 : RowSquare [7,3,2,2,1,1] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg66 sg809

lemma sg4187 : RowSquare [7,3,2,2,1,1] [4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg2076

lemma sg4188 : RowSquare [7,3,2,2,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg13 sg1627

lemma sg4189 : RowSquare [7,3,2,2,1,1] [5,5,5,1] := by
  exact rowSquare_join (by decide) sg181 sg459

lemma sg4190 : RowSquare [7,3,3,1,1,1] [3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1195

lemma sg4191 : RowSquare [7,3,3,1,1,1] [3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1196

lemma sg4192 : RowSquare [7,3,3,1,1,1] [4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg3327

lemma sg4193 : RowSquare [7,3,3,1,1,1] [4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg3332

lemma sg4194 : RowSquare [7,3,3,1,1,1] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg1197

lemma sg4195 : RowSquare [7,3,3,1,1,1] [4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1198

lemma sg4196 : RowSquare [7,3,3,1,1,1] [4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg1199

lemma sg4197 : RowSquare [7,3,3,1,1,1] [4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg62 sg890

lemma sg4198 : RowSquare [7,3,3,1,1,1] [4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg62 sg891

lemma sg4199 : RowSquare [7,3,3,1,1,1] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg62 sg892

lemma sg4200 : RowSquare [7,3,3,1,1,1] [4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg32 sg1200

lemma sg4201 : RowSquare [7,3,3,1,1,1] [5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg3335

lemma sg4202 : RowSquare [7,3,3,1,1,1] [5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg62 sg894

lemma sg4203 : RowSquare [7,3,3,1,1,1] [5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg155 sg519

lemma sg4204 : RowSquare [7,3,3,1,1,1] [5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg1626

lemma sg4205 : RowSquare [7,3,3,1,1,1] [5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg34 sg1198

lemma sg4206 : RowSquare [7,3,3,1,1,1] [5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg88 sg752

lemma sg4207 : RowSquare [7,3,3,1,1,1] [5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg1201

lemma sg4208 : RowSquare [7,3,3,1,1,1] [5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg88 sg753

lemma sg4209 : RowSquare [7,3,3,1,1,1] [5,5,3,3] := by
  exact rowSquare_join (by decide) sg88 sg754

lemma sg4210 : RowSquare [7,3,3,1,1,1] [5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg89 sg753

lemma sg4211 : RowSquare [7,3,3,1,1,1] [5,5,4,2] := by
  exact rowSquare_join (by decide) sg88 sg755

lemma sg4212 : RowSquare [7,3,3,1,1,1] [5,5,5,1] := by
  exact rowSquare_join (by decide) sg89 sg755

lemma sg4213 : RowSquare [7,3,3,1,1,1] [6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg92 sg752

lemma sg4214 : RowSquare [7,3,3,2,1] [3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg123 sg586

lemma sg4215 : RowSquare [7,3,3,2,1] [3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg475

lemma sg4216 : RowSquare [7,3,3,2,1] [3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg476

lemma sg4217 : RowSquare [7,3,3,2,1] [4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg123 sg587

lemma sg4218 : RowSquare [7,3,3,2,1] [4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg478

lemma sg4219 : RowSquare [7,3,3,2,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg285 sg313

lemma sg4220 : RowSquare [7,3,3,2,1] [4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg826

lemma sg4221 : RowSquare [7,3,3,2,1] [4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg285 sg315

lemma sg4222 : RowSquare [7,3,3,2,1] [4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg479

lemma sg4223 : RowSquare [7,3,3,2,1] [4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg181 sg475

lemma sg4224 : RowSquare [7,3,3,2,1] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg286 sg314

lemma sg4225 : RowSquare [7,3,3,2,1] [4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg286 sg315

lemma sg4226 : RowSquare [7,3,3,2,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg287 sg315

lemma sg4227 : RowSquare [7,3,3,2,1] [5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg125 sg587

lemma sg4228 : RowSquare [7,3,3,2,1] [5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg71 sg826

lemma sg4229 : RowSquare [7,3,3,2,1] [5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg371 sg250

lemma sg4230 : RowSquare [7,3,3,2,1] [5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg180 sg478

lemma sg4231 : RowSquare [7,3,3,2,1] [5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg251

lemma sg4232 : RowSquare [7,3,3,2,1] [5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg372 sg250

lemma sg4233 : RowSquare [7,3,3,2,1] [5,5,3,3] := by
  exact rowSquare_join (by decide) sg373 sg250

lemma sg4234 : RowSquare [7,3,3,2,1] [5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg372 sg251

lemma sg4235 : RowSquare [7,3,3,2,1] [5,5,4,2] := by
  exact rowSquare_join (by decide) sg373 sg251

lemma sg4236 : RowSquare [7,3,3,3] [4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg371 sg254

lemma sg4237 : RowSquare [7,3,3,3] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg68 sg834

lemma sg4238 : RowSquare [7,3,3,3] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg373 sg254

lemma sg4239 : RowSquare [7,3,3,3] [5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg179 sg482

lemma sg4240 : RowSquare [7,3,3,3] [5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg374 sg254

lemma sg4241 : RowSquare [7,3,3,3] [5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg182 sg481

lemma sg4242 : RowSquare [7,3,3,3] [5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg484

lemma sg4243 : RowSquare [7,3,3,3] [5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg181 sg482

lemma sg4244 : RowSquare [7,3,3,3] [5,4,4,3] := by
  exact rowSquare_join (by decide) sg254 sg376

lemma sg4245 : RowSquare [7,3,3,3] [5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg371 sg255

lemma sg4246 : RowSquare [7,3,3,3] [5,5,5,1] := by
  exact rowSquare_join (by decide) sg181 sg484

lemma sg4247 : RowSquare [7,3,3,3] [6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg69 sg835

lemma sg4248 : RowSquare [7,3,3,3] [6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg179 sg485

lemma sg4249 : RowSquare [7,3,3,3] [6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg179 sg486

lemma sg4250 : RowSquare [7,3,3,3] [6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg379 sg254

lemma sg4251 : RowSquare [7,3,3,3] [6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg256

lemma sg4252 : RowSquare [7,3,3,3] [6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg372 sg256

lemma sg4253 : RowSquare [7,3,3,3] [6,4,4,2] := by
  exact rowSquare_join (by decide) sg373 sg256

lemma sg4254 : RowSquare [7,3,3,3] [6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg488

lemma sg4255 : RowSquare [7,3,3,3] [6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg375 sg255

lemma sg4256 : RowSquare [7,3,3,3] [6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg180 sg487

lemma sg4257 : RowSquare [7,3,3,3] [6,5,3,2] := by
  exact rowSquare_join (by decide) sg254 sg382

lemma sg4258 : RowSquare [7,3,3,3] [6,5,4,1] := by
  exact rowSquare_join (by decide) sg181 sg487

lemma sg4259 : RowSquare [7,3,3,3] [6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg257

lemma sg4260 : RowSquare [7,3,3,3] [6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg372 sg257

lemma sg4261 : RowSquare [7,3,3,3] [6,6,2,2] := by
  exact rowSquare_join (by decide) sg373 sg257

lemma sg4262 : RowSquare [7,3,3,3] [6,6,3,1] := by
  exact rowSquare_join (by decide) sg255 sg378

lemma sg4263 : RowSquare [7,3,3,3] [6,6,4] := by
  exact rowSquare_join (by decide) sg185 sg484

lemma sg4264 : RowSquare [7,3,3,3] [7,6,1,1,1] := by
  exact rowSquare_join (by decide) sg375 sg257

lemma sg4265 : RowSquare [7,3,3,3] [7,6,2,1] := by
  exact rowSquare_join (by decide) sg376 sg257

lemma sg4266 : RowSquare [7,3,3,3] [7,6,3] := by
  exact rowSquare_join (by decide) sg184 sg488

lemma sg4267 : RowSquare [7,4,1,1,1,1,1] [4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1664

lemma sg4268 : RowSquare [7,4,1,1,1,1,1] [4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1665

lemma sg4269 : RowSquare [7,4,1,1,1,1,1] [4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg16 sg1632

lemma sg4270 : RowSquare [7,4,1,1,1,1,1] [4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg1663

lemma sg4271 : RowSquare [7,4,1,1,1,1,1] [4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1632

lemma sg4272 : RowSquare [7,4,1,1,1,1,1] [4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1666

lemma sg4273 : RowSquare [7,4,1,1,1,1,1] [4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg2123

lemma sg4274 : RowSquare [7,4,1,1,1,1,1] [4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1667

lemma sg4275 : RowSquare [7,4,1,1,1,1,1] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg4 sg2124

lemma sg4276 : RowSquare [7,4,1,1,1,1,1] [5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1668

lemma sg4277 : RowSquare [7,4,1,1,1,1,1] [5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2126

lemma sg4278 : RowSquare [7,4,1,1,1,1,1] [5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1669

lemma sg4279 : RowSquare [7,4,1,1,1,1,1] [5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18 sg1632

lemma sg4280 : RowSquare [7,4,1,1,1,1,1] [5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2127

lemma sg4281 : RowSquare [7,4,1,1,1,1,1] [5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg1185

lemma sg4282 : RowSquare [7,4,1,1,1,1,1] [5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg16 sg1634

lemma sg4283 : RowSquare [7,4,1,1,1,1,1] [5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg39 sg1186

lemma sg4284 : RowSquare [7,4,1,1,1,1,1] [5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg39 sg1187

lemma sg4285 : RowSquare [7,4,1,1,1,1,1] [5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg1664

lemma sg4286 : RowSquare [7,4,1,1,1,1,1] [5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg1665

lemma sg4287 : RowSquare [7,4,1,1,1,1,1] [5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg1188

lemma sg4288 : RowSquare [7,4,1,1,1,1,1] [5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg17 sg1634

lemma sg4289 : RowSquare [7,4,1,1,1,1,1] [5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg1185

lemma sg4290 : RowSquare [7,4,1,1,1,1,1] [5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg1189

lemma sg4291 : RowSquare [7,4,1,1,1,1,1] [5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg40 sg1187

lemma sg4292 : RowSquare [7,4,1,1,1,1,1] [5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2129

lemma sg4293 : RowSquare [7,4,1,1,1,1,1] [5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg1188

lemma sg4294 : RowSquare [7,4,1,1,1,1,1] [5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1670

lemma sg4295 : RowSquare [7,4,1,1,1,1,1] [5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg17 sg1636

lemma sg4296 : RowSquare [7,4,1,1,1,1,1] [5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg1189

lemma sg4297 : RowSquare [7,4,1,1,1,1,1] [5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg40 sg1190

lemma sg4298 : RowSquare [7,4,1,1,1,1,1] [6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19 sg1632

lemma sg4299 : RowSquare [7,4,1,1,1,1,1] [6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1640

lemma sg4300 : RowSquare [7,4,1,1,1,1,1] [6,6,2,2] := by
  exact rowSquare_join (by decide) sg13 sg1671

lemma sg4301 : RowSquare [7,4,1,1,1,1,1] [7,7,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1672

lemma sg4302 : RowSquare [7,4,2,1,1,1] [3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg807

lemma sg4303 : RowSquare [7,4,2,1,1,1] [3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg74 sg808

lemma sg4304 : RowSquare [7,4,2,1,1,1] [3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg809

lemma sg4305 : RowSquare [7,4,2,1,1,1] [4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg2633

lemma sg4306 : RowSquare [7,4,2,1,1,1] [4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg1196

lemma sg4307 : RowSquare [7,4,2,1,1,1] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg87 sg762

lemma sg4308 : RowSquare [7,4,2,1,1,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg814

lemma sg4309 : RowSquare [7,4,2,1,1,1] [4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg815

lemma sg4310 : RowSquare [7,4,2,1,1,1] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg89 sg762

lemma sg4311 : RowSquare [7,4,2,1,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg13 sg1675

lemma sg4312 : RowSquare [7,4,2,1,1,1] [5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg194 sg455

lemma sg4313 : RowSquare [7,4,2,1,1,1] [5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg807

lemma sg4314 : RowSquare [7,4,2,1,1,1] [5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg194 sg457

lemma sg4315 : RowSquare [7,4,2,1,1,1] [5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg194 sg459

lemma sg4316 : RowSquare [7,4,3,1,1] [2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2137

lemma sg4317 : RowSquare [7,4,3,1,1] [3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg306 sg312

lemma sg4318 : RowSquare [7,4,3,1,1] [3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg827

lemma sg4319 : RowSquare [7,4,3,1,1] [3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg306 sg315

lemma sg4320 : RowSquare [7,4,3,1,1] [3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg74 sg828

lemma sg4321 : RowSquare [7,4,3,1,1] [3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg829

lemma sg4322 : RowSquare [7,4,3,1,1] [4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg307 sg312

lemma sg4323 : RowSquare [7,4,3,1,1] [4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg1685

lemma sg4324 : RowSquare [7,4,3,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg350 sg271

lemma sg4325 : RowSquare [7,4,3,2] [3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg285

lemma sg4326 : RowSquare [7,4,3,2] [3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg511

lemma sg4327 : RowSquare [7,4,3,2] [3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg286

lemma sg4328 : RowSquare [7,4,3,2] [3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg74 sg833

lemma sg4329 : RowSquare [7,4,3,2] [3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg834

lemma sg4330 : RowSquare [7,4,3,2] [4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg66 sg850

lemma sg4331 : RowSquare [7,4,3,2] [4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg512

lemma sg4332 : RowSquare [7,4,3,2] [4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg67 sg850

lemma sg4333 : RowSquare [7,4,3,2] [4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg850

lemma sg4334 : RowSquare [7,4,3,2] [4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg290

lemma sg4335 : RowSquare [7,4,3,2] [4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg514

lemma sg4336 : RowSquare [7,4,3,2] [5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg69 sg850

lemma sg4337 : RowSquare [7,4,3,2] [5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg70 sg850

lemma sg4338 : RowSquare [7,4,3,2] [5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg71 sg850

lemma sg4339 : RowSquare [7,4,3,2] [5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg293

lemma sg4340 : RowSquare [7,4,3,2] [5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg515

lemma sg4341 : RowSquare [7,4,4,1] [2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg516

lemma sg4342 : RowSquare [7,4,4,1] [3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg516

lemma sg4343 : RowSquare [7,6,1,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg364 sg271

lemma sg4344 : RowSquare [7,6,2,1] [3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg849

lemma sg4346 : RowSquare [8,2,1,1,1,1,1,1] [2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg425 sg235

lemma sg4347 : RowSquare [8,2,1,1,1,1,1,1] [2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg232 sg430

lemma sg4348 : RowSquare [8,2,1,1,1,1,1,1] [2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg232 sg429

lemma sg4349 : RowSquare [8,2,1,1,1,1,1,1] [2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg1184

lemma sg4350 : RowSquare [8,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1662

lemma sg4351 : RowSquare [8,2,1,1,1,1,1,1] [3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg1662

lemma sg4352 : RowSquare [8,2,1,1,1,1,1,1] [3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg231 sg428

lemma sg4353 : RowSquare [8,2,1,1,1,1,1,1] [3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg1183

lemma sg4354 : RowSquare [8,2,1,1,1,1,1,1] [3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1661

lemma sg4355 : RowSquare [8,2,1,1,1,1,1,1] [3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg104 sg731

lemma sg4356 : RowSquare [8,2,1,1,1,1,1,1] [4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1660

lemma sg4357 : RowSquare [8,2,1,1,1,1,1,1] [5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg3378

lemma sg4358 : RowSquare [8,2,2,2,1,1] [4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg67 sg889

lemma sg4359 : RowSquare [8,2,2,2,2] [4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg312 sg312

lemma sg4360 : RowSquare [8,2,2,2,2] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg313 sg313

lemma sg4361 : RowSquare [8,2,2,2,2] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg315 sg315

lemma sg4362 : RowSquare [8,2,2,2,2] [5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg135 sg586

lemma sg4363 : RowSquare [8,2,2,2,2] [5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg313 sg316

lemma sg4364 : RowSquare [8,2,2,2,2] [5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg132 sg590

lemma sg4365 : RowSquare [8,2,2,2,2] [6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg316 sg316

lemma sg4366 : RowSquare [8,3,1,1,1,1,1] [4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg2708

lemma sg4367 : RowSquare [8,3,1,1,1,1,1] [4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg1750

lemma sg4368 : RowSquare [8,3,1,1,1,1,1] [5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg2709

lemma sg4369 : RowSquare [8,3,1,1,1,1,1] [5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg2710

lemma sg4370 : RowSquare [8,3,1,1,1,1,1] [5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg1242

lemma sg4371 : RowSquare [8,3,1,1,1,1,1] [5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1666

lemma sg4372 : RowSquare [8,3,1,1,1,1,1] [5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1667

lemma sg4373 : RowSquare [8,3,1,1,1,1,1] [6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1670

lemma sg4374 : RowSquare [8,3,2,1,1,1] [3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1257

lemma sg4375 : RowSquare [8,3,2,1,1,1] [3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg888

lemma sg4376 : RowSquare [8,3,2,1,1,1] [3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg889

lemma sg4377 : RowSquare [8,3,2,1,1,1] [3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg890

lemma sg4378 : RowSquare [8,3,2,1,1,1] [3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg74 sg891

lemma sg4379 : RowSquare [8,3,2,1,1,1] [3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg892

lemma sg4380 : RowSquare [8,3,2,1,1,1] [4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg893

lemma sg4381 : RowSquare [8,3,2,1,1,1] [4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg2633

lemma sg4382 : RowSquare [8,3,2,1,1,1] [4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg894

lemma sg4383 : RowSquare [8,3,2,1,1,1] [4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg87 sg807

lemma sg4384 : RowSquare [8,3,2,1,1,1] [4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg895

lemma sg4385 : RowSquare [8,3,2,1,1,1] [4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg1331

lemma sg4386 : RowSquare [8,3,2,1,1,1] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg87 sg809

lemma sg4387 : RowSquare [8,3,2,1,1,1] [4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg27 sg1329

lemma sg4388 : RowSquare [8,3,2,1,1,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg897

lemma sg4389 : RowSquare [8,3,2,1,1,1] [4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg807

lemma sg4390 : RowSquare [8,3,2,1,1,1] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg89 sg809

lemma sg4391 : RowSquare [8,3,2,1,1,1] [5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg193 sg517

lemma sg4392 : RowSquare [8,3,2,1,1,1] [5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg194 sg517

lemma sg4393 : RowSquare [8,3,2,1,1,1] [5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg89 sg815

lemma sg4394 : RowSquare [8,3,2,1,1,1] [6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg196 sg517

lemma sg4395 : RowSquare [8,3,2,2,1] [3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg143 sg586

lemma sg4396 : RowSquare [8,3,2,2,1] [3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg313

lemma sg4397 : RowSquare [8,3,2,2,1] [3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg535

lemma sg4398 : RowSquare [8,3,2,2,1] [3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg314

lemma sg4399 : RowSquare [8,3,2,2,1] [3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg315

lemma sg4400 : RowSquare [8,3,2,2,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg332 sg313

lemma sg4401 : RowSquare [8,3,2,2,1] [4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg270

lemma sg4402 : RowSquare [8,3,2,2,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg373 sg271

lemma sg4403 : RowSquare [8,3,3,1,1] [3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg155 sg586

lemma sg4404 : RowSquare [8,3,3,1,1] [4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg312 sg348

lemma sg4405 : RowSquare [8,3,3,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg350 sg315

lemma sg4406 : RowSquare [8,3,3,1,1] [5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg312 sg351

lemma sg4407 : RowSquare [8,3,3,2] [4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg67 sg940

lemma sg4408 : RowSquare [8,3,3,2] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg285

lemma sg4409 : RowSquare [8,3,3,2] [4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg940

lemma sg4410 : RowSquare [8,3,3,2] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg373 sg287

lemma sg4411 : RowSquare [8,3,3,2] [5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg71 sg940

lemma sg4412 : RowSquare [8,4,1,1,1,1] [3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1758

lemma sg4413 : RowSquare [8,4,1,1,1,1] [4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg1758

lemma sg4414 : RowSquare [8,4,1,1,1,1] [5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg1763

lemma sg4415 : RowSquare [8,4,2,1,1] [3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg912

lemma sg4416 : RowSquare [8,4,2,1,1] [3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg74 sg914

lemma sg4417 : RowSquare [8,4,2,1,1] [3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg915

lemma sg4418 : RowSquare [8,4,2,2] [2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg330 sg330

lemma sg4419 : RowSquare [8,4,2,2] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg373 sg297

lemma sg4420 : RowSquare [8,4,3,1] [3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg577

lemma sg4421 : RowSquare [9,2,1,1,1,1,1] [2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2251

lemma sg4422 : RowSquare [9,2,1,1,1,1,1] [3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2256

lemma sg4423 : RowSquare [9,2,1,1,1,1,1] [4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2260

lemma sg4424 : RowSquare [9,2,1,1,1,1,1] [5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg2256

lemma sg4425 : RowSquare [9,2,1,1,1,1,1] [5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg2710

lemma sg4426 : RowSquare [9,2,1,1,1,1,1] [5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg2260

lemma sg4427 : RowSquare [9,2,1,1,1,1,1] [5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1749

lemma sg4428 : RowSquare [9,2,1,1,1,1,1] [5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg17 sg1750

lemma sg4429 : RowSquare [9,2,1,1,1,1,1] [5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2265

lemma sg4430 : RowSquare [9,2,1,1,1,1,1] [5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2266

lemma sg4431 : RowSquare [9,2,1,1,1,1,1] [5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2267

lemma sg4432 : RowSquare [9,2,1,1,1,1,1] [6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg46 sg1244

lemma sg4433 : RowSquare [9,2,1,1,1,1,1] [6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1751

lemma sg4434 : RowSquare [9,2,2,1,1,1] [2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1327

lemma sg4435 : RowSquare [9,2,2,1,1,1] [3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1329

lemma sg4436 : RowSquare [9,2,2,1,1,1] [3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1330

lemma sg4437 : RowSquare [9,2,2,1,1,1] [3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1331

lemma sg4438 : RowSquare [9,2,2,1,1,1] [3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg1332

lemma sg4439 : RowSquare [9,2,2,2,1] [2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg586

lemma sg4440 : RowSquare [9,2,2,2,1] [3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg586

lemma sg4441 : RowSquare [9,2,2,2,1] [3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg588

lemma sg4442 : RowSquare [9,2,2,2,1] [3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg181 sg586

lemma sg4443 : RowSquare [9,2,2,2,1] [3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg589

lemma sg4444 : RowSquare [9,2,2,2,1] [4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg184 sg586

lemma sg4445 : RowSquare [9,2,2,2,1] [4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg181 sg587

lemma sg4446 : RowSquare [9,2,2,2,1] [4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg179 sg589

lemma sg4447 : RowSquare [9,2,2,2,1] [4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg179 sg590

lemma sg4448 : RowSquare [9,2,2,2,1] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg66 sg1001

lemma sg4449 : RowSquare [9,2,2,2,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg313

lemma sg4450 : RowSquare [9,2,2,2,1] [4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg371 sg315

lemma sg4451 : RowSquare [9,2,2,2,1] [4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg180 sg590

lemma sg4452 : RowSquare [9,2,2,2,1] [4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg181 sg589

lemma sg4453 : RowSquare [9,2,2,2,1] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg372 sg314

lemma sg4454 : RowSquare [9,2,2,2,1] [4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg372 sg315

lemma sg4455 : RowSquare [9,2,2,2,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg373 sg315

lemma sg4456 : RowSquare [9,2,2,2,1] [5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg186 sg586

lemma sg4457 : RowSquare [9,2,2,2,1] [5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg184 sg587

lemma sg4458 : RowSquare [9,2,2,2,1] [5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg371 sg319

lemma sg4459 : RowSquare [9,2,2,2,1] [5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg180 sg595

lemma sg4460 : RowSquare [9,2,2,2,1] [5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg320

lemma sg4461 : RowSquare [9,2,2,2,1] [5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg372 sg319

lemma sg4462 : RowSquare [9,2,2,2,1] [5,5,3,3] := by
  exact rowSquare_join (by decide) sg373 sg319

lemma sg4463 : RowSquare [9,3,1,1,1,1] [3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1754

lemma sg4464 : RowSquare [9,3,1,1,1,1] [4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg1331

lemma sg4465 : RowSquare [9,3,1,1,1,1] [4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg1329

lemma sg4466 : RowSquare [9,3,1,1,1,1] [4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg40 sg1332

lemma sg4467 : RowSquare [9,3,1,1,1,1] [4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg890

lemma sg4468 : RowSquare [9,3,1,1,1,1] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg97 sg892

lemma sg4469 : RowSquare [9,3,1,1,1,1] [5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg893

lemma sg4470 : RowSquare [9,3,1,1,1,1] [5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg41 sg1332

lemma sg4471 : RowSquare [9,3,1,1,1,1] [5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg98 sg892

lemma sg4472 : RowSquare [9,3,1,1,1,1] [5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg99 sg892

lemma sg4473 : RowSquare [9,3,1,1,1,1] [5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg895

lemma sg4474 : RowSquare [9,3,1,1,1,1] [5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg97 sg898

lemma sg4475 : RowSquare [9,3,1,1,1,1] [5,5,4,2] := by
  exact rowSquare_join (by decide) sg97 sg899

lemma sg4476 : RowSquare [9,3,1,1,1,1] [6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19 sg1758

lemma sg4477 : RowSquare [9,3,1,1,1,1] [6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg1338

lemma sg4478 : RowSquare [9,3,1,1,1,1] [6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg228 sg518

lemma sg4479 : RowSquare [9,3,1,1,1,1] [6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg228 sg519

lemma sg4480 : RowSquare [9,3,1,1,1,1] [6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1770

lemma sg4481 : RowSquare [9,3,1,1,1,1] [6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg40 sg1348

lemma sg4482 : RowSquare [9,3,1,1,1,1] [6,6,3,1] := by
  exact rowSquare_join (by decide) sg97 sg902

lemma sg4483 : RowSquare [9,3,1,1,1,1] [6,6,4] := by
  exact rowSquare_join (by decide) sg97 sg903

lemma sg4484 : RowSquare [9,3,1,1,1,1] [7,7,2] := by
  exact rowSquare_join (by decide) sg97 sg909

lemma sg4485 : RowSquare [9,3,2,1,1] [3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg194 sg586

lemma sg4486 : RowSquare [9,3,2,1,1] [3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg910

lemma sg4487 : RowSquare [9,3,2,1,1] [3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg999

lemma sg4488 : RowSquare [9,3,2,1,1] [3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg74 sg1000

lemma sg4489 : RowSquare [9,3,2,1,1] [3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg1001

lemma sg4490 : RowSquare [9,3,2,1,1] [4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg312 sg390

lemma sg4491 : RowSquare [9,3,2,1,1] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg87 sg915

lemma sg4492 : RowSquare [9,3,2,1,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg1006

lemma sg4493 : RowSquare [9,3,2,1,1] [4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg313 sg390

lemma sg4494 : RowSquare [9,3,2,1,1] [4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg913

lemma sg4495 : RowSquare [9,3,2,1,1] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg389 sg314

lemma sg4496 : RowSquare [9,3,2,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg390 sg315

lemma sg4497 : RowSquare [9,3,2,1,1] [5,5,3,3] := by
  exact rowSquare_join (by decide) sg390 sg319

lemma sg4498 : RowSquare [9,3,2,1,1] [6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg313 sg396

lemma sg4499 : RowSquare [9,3,2,1,1] [6,6,2,2] := by
  exact rowSquare_join (by decide) sg390 sg324

lemma sg4500 : RowSquare [9,3,2,1,1] [7,7,1,1] := by
  exact rowSquare_join (by decide) sg394 sg324

lemma sg4501 : RowSquare [9,3,2,2] [3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg373

lemma sg4502 : RowSquare [9,3,2,2] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg373 sg334

lemma sg4503 : RowSquare [9,3,3,1] [3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg636

lemma sg4504 : RowSquare [9,3,3,1] [4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg179 sg636

lemma sg4505 : RowSquare [9,3,3,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg350 sg373

lemma sg4506 : RowSquare [9,4,2,1] [3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg390

lemma sg4507 : RowSquare [9,4,2,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg356 sg371

lemma sg4508 : RowSquare [9,4,2,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg390 sg334

lemma sg4509 : RowSquare [9,4,3] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg1063

lemma sg4510 : RowSquare [10,1,1,1,1,1,1] [6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg7 sg2260

lemma sg4511 : RowSquare [10,1,1,1,1,1,1] [6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg2263

lemma sg4512 : RowSquare [10,1,1,1,1,1,1] [7,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg1749

lemma sg4513 : RowSquare [10,1,1,1,1,1,1] [7,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20 sg1750

lemma sg4514 : RowSquare [10,1,1,1,1,1,1] [7,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg2265

lemma sg4515 : RowSquare [10,1,1,1,1,1,1] [7,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg2267

end UniversalTensorSquare
end
end

end OAI
