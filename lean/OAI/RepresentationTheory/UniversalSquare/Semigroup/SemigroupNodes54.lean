import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes51
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes47

namespace OAI

/-! Semigroup Nodes 54. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg22140 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6693

lemma sg22141 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6694

lemma sg22142 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg6474 sg6653

lemma sg22143 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,6,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7623

lemma sg22144 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,6,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6803

lemma sg22145 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,6,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7624

lemma sg22146 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,6,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6804

lemma sg22147 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,6,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6480 sg6639

lemma sg22148 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,6,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg6480 sg6640

lemma sg22149 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,6,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6805

lemma sg22150 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,6,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6480 sg6641

lemma sg22151 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,6,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg6300 sg7373

lemma sg22152 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6479 sg6642

lemma sg22153 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,6,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6439 sg6788

lemma sg22154 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6480 sg6642

lemma sg22155 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,4,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6151 sg7626

lemma sg22156 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,4,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7627

lemma sg22157 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,4,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7628

lemma sg22158 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,4,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7374

lemma sg22159 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,4,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7375

lemma sg22160 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6151 sg7629

lemma sg22161 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7630

lemma sg22162 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7631

lemma sg22163 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7377

lemma sg22164 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7632

lemma sg22165 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7378

lemma sg22166 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6695

lemma sg22167 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7633

lemma sg22168 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7379

lemma sg22169 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,5,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7634

lemma sg22170 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,5,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7380

lemma sg22171 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7381

lemma sg22172 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,5,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6658

lemma sg22173 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7635

lemma sg22174 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7382

lemma sg22175 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6659

lemma sg22176 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6660

lemma sg22177 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7636

lemma sg22178 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7637

lemma sg22179 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7384

lemma sg22180 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7638

lemma sg22181 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7385

lemma sg22182 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7386

lemma sg22183 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6696

lemma sg22184 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7639

lemma sg22185 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7387

lemma sg22186 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7640

lemma sg22187 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7388

lemma sg22188 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6697

lemma sg22189 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6698

lemma sg22190 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7389

lemma sg22191 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6699

lemma sg22192 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7699

lemma sg22193 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,6,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7151

lemma sg22194 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,6,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7641

lemma sg22195 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,6,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7390

lemma sg22196 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,6,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7390

lemma sg22197 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,6,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6667

lemma sg22198 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,6,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7391

lemma sg22199 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,6,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7391

lemma sg22200 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,6,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6417 sg6804

lemma sg22201 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6417 sg6805

lemma sg22202 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6441 sg6788

lemma sg22203 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6421 sg6796

lemma sg22204 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6298 sg7383

lemma sg22205 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7152

lemma sg22206 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6176 sg7505

lemma sg22207 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6303 sg7360

lemma sg22208 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6424 sg6796

lemma sg22209 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7700

lemma sg22210 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7153

lemma sg22211 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6176 sg7506

lemma sg22212 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6413 sg6820

lemma sg22213 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6820

lemma sg22214 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7154

lemma sg22215 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7642

lemma sg22216 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6413 sg6821

lemma sg22217 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6821

lemma sg22218 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6700

lemma sg22219 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7386

lemma sg22220 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7701

lemma sg22221 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7155

lemma sg22222 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7643

lemma sg22223 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6413 sg6822

lemma sg22224 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6822

lemma sg22225 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6413 sg6823

lemma sg22226 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6823

lemma sg22227 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7388

lemma sg22228 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7389

lemma sg22229 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7156

lemma sg22230 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7644

lemma sg22231 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6413 sg6824

lemma sg22232 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6824

lemma sg22233 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7390

lemma sg22234 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7391

lemma sg22235 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7389

lemma sg22236 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,7,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6413 sg6825

lemma sg22237 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,7,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6825

lemma sg22238 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,7,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7390

lemma sg22239 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,7,7,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7391

lemma sg22240 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6151 sg7645

lemma sg22241 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7646

lemma sg22242 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,4,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7647

lemma sg22243 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,4,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7393

lemma sg22244 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7648

lemma sg22245 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7394

lemma sg22246 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,5,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7649

lemma sg22247 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,5,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7650

lemma sg22248 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,5,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7395

lemma sg22249 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,5,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7651

lemma sg22250 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,5,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7396

lemma sg22251 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7397

lemma sg22252 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7652

lemma sg22253 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,5,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7398

lemma sg22254 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7653

lemma sg22255 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7399

lemma sg22256 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7400

lemma sg22257 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6421 sg6808

lemma sg22258 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7706

lemma sg22259 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7166

lemma sg22260 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7654

lemma sg22261 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7401

lemma sg22262 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6424 sg6808

lemma sg22263 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7707

lemma sg22264 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7167

lemma sg22265 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7655

lemma sg22266 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7402

lemma sg22267 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7402

lemma sg22268 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7168

lemma sg22269 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7656

lemma sg22270 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7403

lemma sg22271 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7403

lemma sg22272 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7397

lemma sg22273 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7708

lemma sg22274 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7169

lemma sg22275 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7657

lemma sg22276 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7404

lemma sg22277 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7405

lemma sg22278 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7399

lemma sg22279 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7400

lemma sg22280 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7170

lemma sg22281 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7658

lemma sg22282 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7406

lemma sg22283 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6417 sg6818

lemma sg22284 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6417 sg6819

lemma sg22285 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7400

lemma sg22286 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6314 sg7329

lemma sg22287 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7709

lemma sg22288 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7171

lemma sg22289 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6176 sg7507

lemma sg22290 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7407

lemma sg22291 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7407

lemma sg22292 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7710

lemma sg22293 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7172

lemma sg22294 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6176 sg7508

lemma sg22295 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7408

lemma sg22296 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7409

lemma sg22297 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7403

lemma sg22298 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7173

lemma sg22299 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6176 sg7509

lemma sg22300 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7410

lemma sg22301 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7404

lemma sg22302 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7405

lemma sg22303 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6421 sg6817

lemma sg22304 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7411

lemma sg22305 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7406

lemma sg22306 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7405

lemma sg22307 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,7,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6417 sg6825

lemma sg22308 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,7,7,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7406

lemma sg22309 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,8,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6315 sg7329

lemma sg22310 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,8,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6315 sg7330

lemma sg22311 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,8,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6295 sg7430

lemma sg22312 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,8,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6176 sg7510

lemma sg22313 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,8,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7407

lemma sg22314 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,8,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6295 sg7431

lemma sg22315 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,8,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6176 sg7511

lemma sg22316 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,8,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7407

lemma sg22317 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,8,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7408

lemma sg22318 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,8,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7409

lemma sg22319 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,8,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6424 sg6820

lemma sg22320 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,8,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7410

lemma sg22321 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,8,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7409

lemma sg22322 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,8,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7411

lemma sg22323 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,8,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7410

lemma sg22324 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,8,7,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7411

lemma sg22325 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,8,8,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6424 sg6825

lemma sg22326 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg985 sg15055

lemma sg22327 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg562 sg15606

lemma sg22328 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg958 sg15154

lemma sg22329 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg21189

lemma sg22330 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg21190

lemma sg22331 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg21191

lemma sg22332 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg80 sg21192

lemma sg22333 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6296 sg7412

lemma sg22334 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7711

lemma sg22335 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6169 sg7514

lemma sg22336 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6298 sg7412

lemma sg22337 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,4,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7712

lemma sg22338 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,4,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6377 sg7036

lemma sg22339 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,4,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6297 sg7413

lemma sg22340 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6299 sg7412

lemma sg22341 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,4,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7713

lemma sg22342 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,4,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7414

lemma sg22343 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,4,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6446 sg6770

lemma sg22344 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,4,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7714

lemma sg22345 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6371 sg7078

lemma sg22346 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,4,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6428 sg6806

lemma sg22347 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7415

lemma sg22348 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7416

lemma sg22349 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6371 sg7079

lemma sg22350 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7715

lemma sg22351 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7417

lemma sg22352 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6407 sg6854

lemma sg22353 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6372 sg7077

lemma sg22354 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7716

lemma sg22355 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7414

lemma sg22356 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6409 sg6854

lemma sg22357 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7418

lemma sg22358 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6371 sg7081

lemma sg22359 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6410 sg6854

lemma sg22360 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7419

lemma sg22361 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7416

lemma sg22362 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7717

lemma sg22363 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7414

lemma sg22364 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7420

lemma sg22365 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7421

lemma sg22366 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7416

lemma sg22367 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6371 sg7085

lemma sg22368 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6372 sg7079

lemma sg22369 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7718

lemma sg22370 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7417

lemma sg22371 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6428 sg6814

lemma sg22372 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7422

lemma sg22373 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7719

lemma sg22374 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7417

lemma sg22375 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7423

lemma sg22376 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7424

lemma sg22377 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7419

lemma sg22378 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6372 sg7083

lemma sg22379 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7425

lemma sg22380 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7420

lemma sg22381 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7421

lemma sg22382 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6371 sg7092

lemma sg22383 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7426

lemma sg22384 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7420

lemma sg22385 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,6,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7421

lemma sg22386 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,7,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6315 sg7343

lemma sg22387 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,7,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6372 sg7086

lemma sg22388 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,7,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6311 sg7360

lemma sg22389 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,7,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7427

lemma sg22390 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,7,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6372 sg7087

lemma sg22391 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,7,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7428

lemma sg22392 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,7,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7423

lemma sg22393 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,7,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7424

lemma sg22394 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,7,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7429

lemma sg22395 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,7,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7425

lemma sg22396 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,7,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7424

lemma sg22397 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,7,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7426

lemma sg22398 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,7,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7425

lemma sg22399 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,7,7,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7426

lemma sg22400 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,8,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6315 sg7351

lemma sg22401 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,8,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6314 sg7360

lemma sg22402 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,8,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7430

lemma sg22403 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,8,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7427

lemma sg22404 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,8,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7431

lemma sg22405 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,8,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7428

lemma sg22406 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,8,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6315 sg7357

lemma sg22407 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,8,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7429

lemma sg22408 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,8,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7428

lemma sg22409 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,8,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7429

lemma sg22410 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,8,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6021 sg7811

lemma sg22411 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,9,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6315 sg7360

lemma sg22412 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,9,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6315 sg7361

lemma sg22413 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,9,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7430

lemma sg22414 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,9,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7431

lemma sg22415 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,9,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7430

lemma sg22416 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,9,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7431

lemma sg22417 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,9,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6022 sg7811

lemma sg22418 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg25 sg21273

lemma sg22419 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg25 sg21274

lemma sg22420 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg25 sg21275

lemma sg22421 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg25 sg21276

lemma sg22422 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg24 sg21277

lemma sg22423 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg24 sg21278

lemma sg22424 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg24 sg21279

lemma sg22425 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,2,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg24 sg21280

lemma sg22426 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,2,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg24 sg21281

lemma sg22427 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1288 sg14753

lemma sg22428 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg72 sg21195

lemma sg22429 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg72 sg21196

lemma sg22430 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg72 sg21197

lemma sg22431 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg72 sg21198

lemma sg22432 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg14748

lemma sg22433 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1702 sg14410

lemma sg22434 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg126 sg21080

lemma sg22435 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg126 sg21081

lemma sg22436 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg126 sg21082

lemma sg22437 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg126 sg21083

lemma sg22438 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg962 sg15153

lemma sg22439 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg145 sg21072

lemma sg22440 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg15223

lemma sg22441 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg145 sg21073

lemma sg22442 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg145 sg21074

lemma sg22443 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg145 sg21075

lemma sg22444 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg967 sg15152

lemma sg22445 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1309 sg14714

lemma sg22446 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6234 sg7483

lemma sg22447 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7100

lemma sg22448 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6164 sg7539

lemma sg22449 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5510 sg8627

lemma sg22450 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5298 sg8784

lemma sg22451 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg331 sg19574

lemma sg22452 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6235 sg7483

lemma sg22453 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7101

lemma sg22454 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7045

lemma sg22455 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6167 sg7519

lemma sg22456 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5511 sg8620

lemma sg22457 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7102

lemma sg22458 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7046

lemma sg22459 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6378 sg7028

lemma sg22460 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6170 sg7513

lemma sg22461 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5513 sg8616

lemma sg22462 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6378 sg7029

lemma sg22463 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6385 sg7025

lemma sg22464 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6174 sg7512

lemma sg22465 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg5665 sg8271

lemma sg22466 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg5514 sg8615

lemma sg22467 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1288 sg14754

lemma sg22468 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg73 sg21195

lemma sg22469 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg73 sg21196

lemma sg22470 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg73 sg21197

lemma sg22471 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg73 sg21198

lemma sg22472 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg14749

lemma sg22473 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1702 sg14411

lemma sg22474 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg127 sg21080

lemma sg22475 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg127 sg21081

lemma sg22476 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg127 sg21082

lemma sg22477 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg127 sg21083

lemma sg22478 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1290 sg14748

lemma sg22479 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1709 sg14406

lemma sg22480 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1702 sg14412

lemma sg22481 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg146 sg21073

lemma sg22482 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg146 sg21074

lemma sg22483 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg146 sg21075

lemma sg22484 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg963 sg15153

lemma sg22485 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1309 sg14716

lemma sg22486 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6236 sg7483

lemma sg22487 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7103

lemma sg22488 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6164 sg7541

lemma sg22489 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5510 sg8628

lemma sg22490 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5298 sg8785

lemma sg22491 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg987 sg15054

lemma sg22492 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1310 sg14714

lemma sg22493 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6237 sg7483

lemma sg22494 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7104

lemma sg22495 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7047

lemma sg22496 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6167 sg7520

lemma sg22497 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5511 sg8621

lemma sg22498 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6238 sg7483

lemma sg22499 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7105

lemma sg22500 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7048

lemma sg22501 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7045

lemma sg22502 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6168 sg7519

lemma sg22503 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5512 sg8620

lemma sg22504 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7049

lemma sg22505 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7046

lemma sg22506 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6379 sg7028

lemma sg22507 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6171 sg7513

lemma sg22508 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6379 sg7029

lemma sg22509 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6386 sg7025

lemma sg22510 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6175 sg7512

lemma sg22511 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg5666 sg8271

lemma sg22512 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1309 sg14717

lemma sg22513 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1709 sg14407

lemma sg22514 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1702 sg14413

lemma sg22515 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg147 sg21073

lemma sg22516 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg147 sg21074

lemma sg22517 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg147 sg21075

lemma sg22518 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1302 sg14720

lemma sg22519 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1703 sg14410

lemma sg22520 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6239 sg7483

lemma sg22521 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7106

lemma sg22522 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6164 sg7544

lemma sg22523 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5510 sg8629

lemma sg22524 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5298 sg8786

lemma sg22525 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg983 sg15056

lemma sg22526 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1302 sg14721

lemma sg22527 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6240 sg7483

lemma sg22528 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7107

lemma sg22529 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7050

lemma sg22530 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6167 sg7521

lemma sg22531 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5511 sg8622

lemma sg22532 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1311 sg14714

lemma sg22533 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6241 sg7483

lemma sg22534 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7108

lemma sg22535 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7051

lemma sg22536 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6378 sg7031

lemma sg22537 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6170 sg7515

lemma sg22538 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5513 sg8617

lemma sg22539 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7109

end UniversalTensorSquare
end
end

end OAI
