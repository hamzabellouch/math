import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes12
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes15

namespace OAI

/-! Semigroup Nodes 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8137 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg614 sg1893

lemma sg8138 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg371 sg2314

lemma sg8139 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg2397

lemma sg8140 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1031 sg1409

lemma sg8141 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1896

lemma sg8142 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1031 sg1410

lemma sg8143 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg615 sg1893

lemma sg8144 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg2398

lemma sg8145 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg1410

lemma sg8146 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg940 sg1520

lemma sg8147 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1521

lemma sg8148 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1031 sg1411

lemma sg8149 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg2401

lemma sg8150 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1032 sg1411

lemma sg8151 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg1411

lemma sg8152 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg371 sg2317

lemma sg8153 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1522

lemma sg8154 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg941 sg1521

lemma sg8155 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1523

lemma sg8156 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg1412

lemma sg8157 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg942 sg1521

lemma sg8158 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg943 sg1521

lemma sg8159 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg390 sg2285

lemma sg8160 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1032 sg1412

lemma sg8161 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg1033 sg1412

lemma sg8162 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg2402

lemma sg8163 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg1413

lemma sg8164 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg941 sg1523

lemma sg8165 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg1032 sg1413

lemma sg8166 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg942 sg1523

lemma sg8167 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg373 sg2319

lemma sg8168 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [6,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg1414

lemma sg8169 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [6,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg1415

lemma sg8170 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [6,5,5,4,1] := by
  exact rowSquare_join (by decide) sg947 sg1523

lemma sg8171 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [6,5,5,5] := by
  exact rowSquare_join (by decide) sg373 sg2323

lemma sg8172 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [8,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1531

lemma sg8173 : RowSquare [5,3,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1533

lemma sg8174 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1033 sg1502

lemma sg8175 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg1524

lemma sg8176 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1034 sg1500

lemma sg8177 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1003 sg1520

lemma sg8178 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1034 sg1503

lemma sg8179 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1520

lemma sg8180 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1521

lemma sg8181 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg1416

lemma sg8182 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1417

lemma sg8183 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1522

lemma sg8184 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1416

lemma sg8185 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1523

lemma sg8186 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1416

lemma sg8187 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg1417

lemma sg8188 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1416

lemma sg8189 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1908

lemma sg8190 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1417

lemma sg8191 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1417

lemma sg8192 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1003 sg1417

lemma sg8193 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1526

lemma sg8194 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1908

lemma sg8195 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1005 sg1417

lemma sg8196 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg1422

lemma sg8197 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1422

lemma sg8198 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1422

lemma sg8199 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1529

lemma sg8200 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1031 sg1377

lemma sg8201 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1424

lemma sg8202 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg1377

lemma sg8203 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1033 sg1377

lemma sg8204 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1008 sg1417

lemma sg8205 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1424

lemma sg8206 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg1001 sg1424

lemma sg8207 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg1878

lemma sg8208 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg590 sg1908

lemma sg8209 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1006 sg1422

lemma sg8210 : RowSquare [5,4,3,2,1,1,1,1,1,1,1] [5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg0 sg6642

lemma sg8211 : RowSquare [5,4,3,2,1,1,1,1,1,1,1] [6,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg6653

lemma sg8212 : RowSquare [5,4,3,2,1,1,1,1,1,1,1] [7,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg5820

lemma sg8213 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1001 sg1502

lemma sg8214 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg1503

lemma sg8215 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1002 sg1500

lemma sg8216 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1002 sg1503

lemma sg8217 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1510

lemma sg8218 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1] [7,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1003 sg1504

lemma sg8219 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg1874

lemma sg8220 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg910 sg1498

lemma sg8221 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1499

lemma sg8222 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg1875

lemma sg8223 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1500

lemma sg8224 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg1876

lemma sg8225 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1501

lemma sg8226 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1502

lemma sg8227 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1877

lemma sg8228 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1878

lemma sg8229 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1879

lemma sg8230 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1503

lemma sg8231 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg997 sg1372

lemma sg8232 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1504

lemma sg8233 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg1373

lemma sg8234 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1505

lemma sg8235 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg587 sg1876

lemma sg8236 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1506

lemma sg8237 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1507

lemma sg8238 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg1373

lemma sg8239 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1508

lemma sg8240 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1509

lemma sg8241 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1882

lemma sg8242 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1878

lemma sg8243 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg1374

lemma sg8244 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1379

lemma sg8245 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1879

lemma sg8246 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1883

lemma sg8247 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1884

lemma sg8248 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1377

lemma sg8249 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1885

lemma sg8250 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1886

lemma sg8251 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1378

lemma sg8252 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1379

lemma sg8253 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1879

lemma sg8254 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1378

lemma sg8255 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg589 sg1878

lemma sg8256 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1379

lemma sg8257 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1378

lemma sg8258 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,3] := by
  exact rowSquare_join (by decide) sg1001 sg1378

lemma sg8259 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1379

lemma sg8260 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,2] := by
  exact rowSquare_join (by decide) sg1001 sg1379

lemma sg8261 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1512

lemma sg8262 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [6,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1513

lemma sg8263 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [6,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1514

lemma sg8264 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [6,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1515

lemma sg8265 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,1] := by
  exact rowSquare_join (by decide) sg1005 sg1379

lemma sg8266 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [6,6,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1888

lemma sg8267 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [6,6,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1889

lemma sg8268 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [6,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1388

lemma sg8269 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [6,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1389

lemma sg8270 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [7,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1516

lemma sg8271 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg910 sg1371

lemma sg8272 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [5,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg1778

lemma sg8273 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg590 sg1782

lemma sg8274 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [6,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1 sg5902

lemma sg8275 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [6,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1399

lemma sg8276 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [7,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg5910

lemma sg8277 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [7,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg4559

lemma sg8278 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [7,4,4,3,3] := by
  exact rowSquare_join (by decide) sg1 sg5911

lemma sg8279 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [7,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4560

lemma sg8280 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [7,4,4,4,2] := by
  exact rowSquare_join (by decide) sg13 sg4561

lemma sg8281 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [7,7,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1793

lemma sg8282 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [7,7,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1287

lemma sg8283 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [7,7,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1791

lemma sg8284 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [7,7,2,2,2,1] := by
  exact rowSquare_join (by decide) sg595 sg1785

lemma sg8285 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [8,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5915

lemma sg8286 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [8,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg4562

lemma sg8287 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [8,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg5916

lemma sg8288 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [8,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg5917

lemma sg8289 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [8,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg5918

lemma sg8290 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [9,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4563

lemma sg8291 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [9,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg5921

lemma sg8292 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [9,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg4564

lemma sg8293 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [9,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg5922

lemma sg8294 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [9,4,4,4] := by
  exact rowSquare_join (by decide) sg13 sg4565

lemma sg8295 : RowSquare [5,5,2,2,2,2,2,1] [4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg3998

lemma sg8296 : RowSquare [5,5,2,2,2,2,2,1] [4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg3998

lemma sg8297 : RowSquare [5,5,2,2,2,2,2,1] [5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg3998

lemma sg8298 : RowSquare [5,5,2,2,2,2,2,1] [5,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg3999

lemma sg8299 : RowSquare [5,5,2,2,2,2,2,1] [5,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg3999

lemma sg8300 : RowSquare [5,5,2,2,2,2,2,1] [5,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4006

lemma sg8301 : RowSquare [5,5,2,2,2,2,2,1] [5,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4007

lemma sg8302 : RowSquare [5,5,2,2,2,2,2,1] [5,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg4001

lemma sg8303 : RowSquare [5,5,2,2,2,2,2,1] [5,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg4002

lemma sg8304 : RowSquare [5,5,2,2,2,2,2,1] [5,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg4003

lemma sg8305 : RowSquare [5,5,2,2,2,2,2,1] [5,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg41 sg4004

lemma sg8306 : RowSquare [5,5,2,2,2,2,2,1] [5,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4008

lemma sg8307 : RowSquare [5,5,2,2,2,2,2,1] [5,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4009

lemma sg8308 : RowSquare [5,5,2,2,2,2,2,1] [5,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4010

lemma sg8309 : RowSquare [5,5,2,2,2,2,2,1] [5,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg39 sg4011

lemma sg8310 : RowSquare [5,5,2,2,2,2,2,1] [5,4,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg4000

lemma sg8311 : RowSquare [5,5,2,2,2,2,2,1] [5,4,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4007

lemma sg8312 : RowSquare [5,5,2,2,2,2,2,1] [5,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg4002

lemma sg8313 : RowSquare [5,5,2,2,2,2,2,1] [5,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg4003

lemma sg8314 : RowSquare [5,5,2,2,2,2,2,1] [5,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg42 sg4004

lemma sg8315 : RowSquare [5,5,2,2,2,2,2,1] [5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg42 sg4005

lemma sg8316 : RowSquare [5,5,2,2,2,2,2,1] [5,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4009

lemma sg8317 : RowSquare [5,5,2,2,2,2,2,1] [5,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4014

lemma sg8318 : RowSquare [5,5,2,2,2,2,2,1] [5,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4017

lemma sg8319 : RowSquare [5,5,2,2,2,2,2,1] [5,5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4013

lemma sg8320 : RowSquare [5,5,2,2,2,2,2,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg3998

lemma sg8321 : RowSquare [5,5,2,2,2,2,2,1] [6,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg3999

lemma sg8322 : RowSquare [5,5,2,2,2,2,2,1] [6,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg4006

lemma sg8323 : RowSquare [5,5,2,2,2,2,2,1] [6,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg4006

lemma sg8324 : RowSquare [5,5,2,2,2,2,2,1] [6,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4018

lemma sg8325 : RowSquare [5,5,2,2,2,2,2,1] [6,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg4002

lemma sg8326 : RowSquare [5,5,2,2,2,2,2,1] [6,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg4003

lemma sg8327 : RowSquare [5,5,2,2,2,2,2,1] [6,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg43 sg4004

lemma sg8328 : RowSquare [5,5,2,2,2,2,2,1] [6,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg4009

lemma sg8329 : RowSquare [5,5,2,2,2,2,2,1] [6,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg4007

lemma sg8330 : RowSquare [5,5,2,2,2,2,2,1] [6,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg4009

lemma sg8331 : RowSquare [5,5,2,2,2,2,2,1] [7,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg3999

lemma sg8332 : RowSquare [5,5,2,2,2,2,2,1] [7,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg4006

lemma sg8333 : RowSquare [5,5,2,2,2,2,2,1] [7,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg4018

lemma sg8334 : RowSquare [5,5,2,2,2,2,2,1] [7,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg4002

lemma sg8335 : RowSquare [5,5,2,2,2,2,2,1] [7,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg4003

lemma sg8336 : RowSquare [5,5,2,2,2,2,2,1] [7,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg44 sg4004

lemma sg8337 : RowSquare [5,5,2,2,2,2,2,1] [7,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg4018

lemma sg8338 : RowSquare [5,5,2,2,2,2,2,1] [7,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg4009

lemma sg8339 : RowSquare [5,5,2,2,2,2,2,1] [8,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg4006

lemma sg8340 : RowSquare [5,5,2,2,2,2,2,1] [8,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg4018

lemma sg8341 : RowSquare [5,5,2,2,2,2,2,1] [8,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg4009

lemma sg8342 : RowSquare [5,5,2,2,2,2,2,1] [9,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg4018

lemma sg8343 : RowSquare [5,5,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1682

lemma sg8344 : RowSquare [5,5,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1682

lemma sg8345 : RowSquare [5,5,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1683

lemma sg8346 : RowSquare [5,5,3,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1682

lemma sg8347 : RowSquare [5,5,3,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg1684

lemma sg8348 : RowSquare [5,5,3,2,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg589 sg1682

lemma sg8349 : RowSquare [5,5,3,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg1682

lemma sg8350 : RowSquare [5,5,3,2,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg1686

lemma sg8351 : RowSquare [5,5,3,2,1,1,1,1,1,1] [3,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1687

lemma sg8352 : RowSquare [5,5,3,2,1,1,1,1,1,1] [3,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1688

lemma sg8353 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1683

lemma sg8354 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg1223

lemma sg8355 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg592 sg1682

lemma sg8356 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1267

lemma sg8357 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg593 sg1682

lemma sg8358 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1268

lemma sg8359 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg594 sg1682

lemma sg8360 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1269

lemma sg8361 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg587 sg1686

lemma sg8362 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1270

lemma sg8363 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1690

lemma sg8364 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg587 sg1687

lemma sg8365 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1688

lemma sg8366 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg595 sg1682

lemma sg8367 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1684

lemma sg8368 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg1691

lemma sg8369 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg596 sg1682

lemma sg8370 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg1684

lemma sg8371 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1693

lemma sg8372 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg588 sg1688

lemma sg8373 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1271

lemma sg8374 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1272

lemma sg8375 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg589 sg1687

lemma sg8376 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg589 sg1688

lemma sg8377 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg1686

lemma sg8378 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg590 sg1687

lemma sg8379 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg590 sg1688

lemma sg8380 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg597 sg1682

lemma sg8381 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1273

lemma sg8382 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg591 sg1688

lemma sg8383 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg601 sg1682

lemma sg8384 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg592 sg1688

lemma sg8385 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1001 sg1225

lemma sg8386 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,5,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg602 sg1682

lemma sg8387 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg595 sg1684

lemma sg8388 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1695

lemma sg8389 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg588 sg1691

lemma sg8390 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg1691

lemma sg8391 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg588 sg1692

lemma sg8392 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1693

lemma sg8393 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg595 sg1688

lemma sg8394 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1226

lemma sg8395 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1001 sg1226

lemma sg8396 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg13 sg4571

lemma sg8397 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1696

lemma sg8398 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg589 sg1694

lemma sg8399 : RowSquare [5,5,3,2,1,1,1,1,1,1] [6,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg597 sg1688

lemma sg8400 : RowSquare [5,5,3,2,1,1,1,1,1,1] [6,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1229

lemma sg8401 : RowSquare [5,5,3,2,1,1,1,1,1,1] [6,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg588 sg1695

lemma sg8402 : RowSquare [5,5,3,2,1,1,1,1,1,1] [6,6,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg4571

lemma sg8403 : RowSquare [5,5,3,2,1,1,1,1,1,1] [7,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3 sg5240

lemma sg8404 : RowSquare [5,5,3,2,1,1,1,1,1,1] [8,8,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1697

lemma sg8405 : RowSquare [5,5,3,2,1,1,1,1,1,1] [8,8,2,1,1,1] := by
  exact rowSquare_join (by decide) sg27 sg3786

lemma sg8406 : RowSquare [5,5,3,2,1,1,1,1,1,1] [8,8,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg4579

lemma sg8407 : RowSquare [6,4,1,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1093 sg1332

lemma sg8408 : RowSquare [6,4,1,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1096 sg1332

lemma sg8409 : RowSquare [6,4,2,2,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg613 sg1757

lemma sg8410 : RowSquare [6,4,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg613 sg1758

lemma sg8411 : RowSquare [6,4,2,2,1,1,1,1,1,1,1] [4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg616 sg1757

lemma sg8412 : RowSquare [6,4,2,2,1,1,1,1,1,1,1] [5,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg623 sg1756

lemma sg8413 : RowSquare [6,4,2,2,1,1,1,1,1,1,1] [5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg1766

lemma sg8414 : RowSquare [6,4,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg2626

lemma sg8415 : RowSquare [6,4,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg849 sg1327

lemma sg8416 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg2626

lemma sg8417 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg2627

lemma sg8418 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg850 sg1327

lemma sg8419 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg849 sg1328

lemma sg8420 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg180 sg2626

lemma sg8421 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg549 sg1754

lemma sg8422 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg851 sg1327

lemma sg8423 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg849 sg1329

lemma sg8424 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg181 sg2626

lemma sg8425 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg849 sg1330

lemma sg8426 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg551 sg1754

lemma sg8427 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg1331

lemma sg8428 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg854 sg1327

lemma sg8429 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg1332

lemma sg8430 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg2631

lemma sg8431 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg178 sg2632

lemma sg8432 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg178 sg2633

lemma sg8433 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg182 sg2626

lemma sg8434 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg2627

lemma sg8435 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg855 sg1327

lemma sg8436 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6878

lemma sg8437 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg183 sg2626

lemma sg8438 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg180 sg2627

lemma sg8439 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6879

lemma sg8440 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg856 sg1327

lemma sg8441 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6880

lemma sg8442 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg850 sg1329

lemma sg8443 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg184 sg2626

lemma sg8444 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg181 sg2627

lemma sg8445 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg857 sg1327

lemma sg8446 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6881

lemma sg8447 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg850 sg1330

lemma sg8448 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg850 sg1331

lemma sg8449 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg548 sg1757

lemma sg8450 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg548 sg1758

lemma sg8451 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg179 sg2632

lemma sg8452 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg178 sg2636

lemma sg8453 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg185 sg2626

lemma sg8454 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg552 sg1754

lemma sg8455 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg859 sg1327

lemma sg8456 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg1338

lemma sg8457 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg851 sg1329

lemma sg8458 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg553 sg1754

lemma sg8459 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg851 sg1330

lemma sg8460 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg853 sg1329

lemma sg8461 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg854 sg1329

lemma sg8462 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg178 sg2640

lemma sg8463 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg554 sg1754

lemma sg8464 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg862 sg1327

lemma sg8465 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg550 sg1756

lemma sg8466 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg181 sg2630

lemma sg8467 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg551 sg1756

lemma sg8468 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg4862

lemma sg8469 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg186 sg2626

lemma sg8470 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg182 sg2627

lemma sg8471 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6883

lemma sg8472 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6884

lemma sg8473 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6885

lemma sg8474 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6886

lemma sg8475 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg187 sg2626

lemma sg8476 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg183 sg2627

lemma sg8477 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6887

lemma sg8478 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6888

lemma sg8479 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6889

lemma sg8480 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg184 sg2627

lemma sg8481 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg0 sg6890

lemma sg8482 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,4,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg188 sg2626

lemma sg8483 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,4,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg185 sg2627

lemma sg8484 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg6893

lemma sg8485 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg868 sg1327

lemma sg8486 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg869 sg1327

lemma sg8487 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg554 sg1755

lemma sg8488 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg554 sg1756

lemma sg8489 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5124

lemma sg8490 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg4863

lemma sg8491 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg4864

lemma sg8492 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg189 sg2626

lemma sg8493 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg186 sg2627

lemma sg8494 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6894

lemma sg8495 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg5956

lemma sg8496 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg190 sg2626

lemma sg8497 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg187 sg2627

lemma sg8498 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6895

lemma sg8499 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6896

lemma sg8500 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg6897

lemma sg8501 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg188 sg2627

lemma sg8502 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6898

lemma sg8503 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6899

lemma sg8504 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg870 sg1327

lemma sg8505 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,5,5,5] := by
  exact rowSquare_join (by decide) sg33 sg3768

lemma sg8506 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg871 sg1327

lemma sg8507 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg3160

lemma sg8508 : RowSquare [6,4,3,2,1,1,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6901

lemma sg8509 : RowSquare [6,4,3,2,1,1,1,1,1,1] [7,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg191 sg2626

lemma sg8510 : RowSquare [6,4,3,2,1,1,1,1,1,1] [7,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6023

lemma sg8511 : RowSquare [6,4,3,2,1,1,1,1,1,1] [7,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6024

lemma sg8512 : RowSquare [6,4,3,2,1,1,1,1,1,1] [7,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6025

lemma sg8513 : RowSquare [6,4,3,2,1,1,1,1,1,1] [7,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6026

lemma sg8514 : RowSquare [6,4,3,2,1,1,1,1,1,1] [7,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5131

lemma sg8515 : RowSquare [6,4,3,2,1,1,1,1,1,1] [7,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5132

lemma sg8516 : RowSquare [6,4,3,2,1,1,1,1,1,1] [7,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6902

lemma sg8517 : RowSquare [6,4,3,2,1,1,1,1,1,1] [8,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6903

lemma sg8518 : RowSquare [6,4,3,2,1,1,1,1,1,1] [8,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6027

lemma sg8519 : RowSquare [6,4,3,2,1,1,1,1,1,1] [8,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3 sg5351

lemma sg8520 : RowSquare [6,4,3,2,1,1,1,1,1,1] [8,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6028

lemma sg8521 : RowSquare [6,4,3,2,1,1,1,1,1,1] [8,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3 sg5352

lemma sg8522 : RowSquare [6,4,3,2,1,1,1,1,1,1] [8,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5134

lemma sg8523 : RowSquare [6,4,3,2,1,1,1,1,1,1] [8,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg5132

lemma sg8524 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1327

lemma sg8525 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1327

lemma sg8526 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1327

lemma sg8527 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1327

lemma sg8528 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1327

lemma sg8529 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg1327

lemma sg8530 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg1328

lemma sg8531 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1003 sg1327

lemma sg8532 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1328

lemma sg8533 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg997 sg1329

lemma sg8534 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1004 sg1327

lemma sg8535 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1328

lemma sg8536 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg1330

end UniversalTensorSquare
end
end

end OAI
