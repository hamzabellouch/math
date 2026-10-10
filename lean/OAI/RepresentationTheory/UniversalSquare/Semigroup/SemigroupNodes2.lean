import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes1

namespace OAI

/-! Semigroup Nodes 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1240 : RowSquare [5,1,1,1,1,1,1] [3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg586

lemma sg1241 : RowSquare [5,1,1,1,1,1,1] [3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg998

lemma sg1242 : RowSquare [5,1,1,1,1,1,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg999

lemma sg1243 : RowSquare [5,1,1,1,1,1,1] [3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1000

lemma sg1244 : RowSquare [5,1,1,1,1,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg1001

lemma sg1245 : RowSquare [5,1,1,1,1,1,1] [4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg587

lemma sg1246 : RowSquare [5,1,1,1,1,1,1] [4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg588

lemma sg1247 : RowSquare [5,1,1,1,1,1,1] [4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg589

lemma sg1248 : RowSquare [5,1,1,1,1,1,1] [4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg590

lemma sg1249 : RowSquare [5,1,1,1,1,1,1] [4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1006

lemma sg1250 : RowSquare [5,1,1,1,1,1,1] [4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1007

lemma sg1251 : RowSquare [5,1,1,1,1,1,1] [4,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg1008

lemma sg1252 : RowSquare [5,1,1,1,1,1,1] [5,3,2,1] := by
  exact rowSquare_join (by decide) sg2 sg596

lemma sg1253 : RowSquare [5,1,1,1,1,1,1] [5,4,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1015

lemma sg1254 : RowSquare [5,1,1,1,1,1,1] [5,4,2] := by
  exact rowSquare_join (by decide) sg0 sg1016

lemma sg1255 : RowSquare [5,1,1,1,1,1,1] [6,4,1] := by
  exact rowSquare_join (by decide) sg2 sg602

lemma sg1256 : RowSquare [5,1,1,1,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg0 sg1023

lemma sg1257 : RowSquare [5,2,1,1,1,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg910

lemma sg1258 : RowSquare [5,2,1,1,1,1] [3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg586

lemma sg1259 : RowSquare [5,2,1,1,1,1] [3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg912

lemma sg1260 : RowSquare [5,2,1,1,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg809

lemma sg1261 : RowSquare [5,2,1,1,1,1] [3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg313

lemma sg1262 : RowSquare [5,2,1,1,1,1] [3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg314

lemma sg1263 : RowSquare [5,2,1,1,1,1] [3,3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg315

lemma sg1264 : RowSquare [5,2,1,1,1,1] [4,4,2,1] := by
  exact rowSquare_join (by decide) sg4 sg319

lemma sg1265 : RowSquare [5,2,1,1,1,1] [4,4,3] := by
  exact rowSquare_join (by decide) sg4 sg320

lemma sg1266 : RowSquare [5,2,1,1,1,1] [5,5,1] := by
  exact rowSquare_join (by decide) sg4 sg324

lemma sg1267 : RowSquare [5,2,2,1,1] [3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg826

lemma sg1268 : RowSquare [5,2,2,1,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg827

lemma sg1269 : RowSquare [5,2,2,1,1] [3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg828

lemma sg1270 : RowSquare [5,2,2,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg829

lemma sg1271 : RowSquare [5,2,2,1,1] [3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg270

lemma sg1272 : RowSquare [5,2,2,1,1] [3,3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg271

lemma sg1273 : RowSquare [5,2,2,1,1] [4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg830

lemma sg1274 : RowSquare [5,3,1,1,1] [3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg838

lemma sg1275 : RowSquare [5,3,1,1,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg839

lemma sg1276 : RowSquare [5,3,1,1,1] [3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg840

lemma sg1277 : RowSquare [5,3,1,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg841

lemma sg1278 : RowSquare [5,3,1,1,1] [3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg270

lemma sg1279 : RowSquare [5,3,1,1,1] [3,3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg271

lemma sg1280 : RowSquare [5,3,1,1,1] [4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg534

lemma sg1281 : RowSquare [5,3,1,1,1] [4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg132

lemma sg1282 : RowSquare [5,3,1,1,1] [4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg273

lemma sg1283 : RowSquare [5,3,1,1,1] [4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg133

lemma sg1284 : RowSquare [5,3,1,1,1] [4,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg134

lemma sg1285 : RowSquare [5,3,1,1,1] [4,4,2,1] := by
  exact rowSquare_join (by decide) sg4 sg275

lemma sg1286 : RowSquare [5,3,1,1,1] [4,4,3] := by
  exact rowSquare_join (by decide) sg4 sg276

lemma sg1287 : RowSquare [5,3,1,1,1] [5,5,1] := by
  exact rowSquare_join (by decide) sg17 sg115

lemma sg1288 : RowSquare [5,3,2,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg849

lemma sg1289 : RowSquare [5,3,2,1] [3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg850

lemma sg1290 : RowSquare [5,3,2,1] [3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg851

lemma sg1291 : RowSquare [5,3,2,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg852

lemma sg1292 : RowSquare [5,3,2,1] [3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg285

lemma sg1293 : RowSquare [5,3,2,1] [3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg32 sg55

lemma sg1294 : RowSquare [5,3,2,1] [3,3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg287

lemma sg1295 : RowSquare [5,3,2,1] [4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg511

lemma sg1296 : RowSquare [5,3,2,1] [4,3,3,1] := by
  exact rowSquare_join (by decide) sg33 sg55

lemma sg1297 : RowSquare [5,3,2,1] [4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg143

lemma sg1298 : RowSquare [5,3,2,1] [4,4,2,1] := by
  exact rowSquare_join (by decide) sg27 sg67

lemma sg1299 : RowSquare [5,3,2,1] [4,4,3] := by
  exact rowSquare_join (by decide) sg34 sg55

lemma sg1300 : RowSquare [5,3,3] [3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg516

lemma sg1301 : RowSquare [5,3,3] [4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg876

lemma sg1302 : RowSquare [5,4,1,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg877

lemma sg1303 : RowSquare [5,4,1,1] [3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg142

lemma sg1304 : RowSquare [5,4,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg879

lemma sg1305 : RowSquare [5,4,1,1] [3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg295

lemma sg1306 : RowSquare [5,4,1,1] [3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg143

lemma sg1307 : RowSquare [5,4,1,1] [3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg296

lemma sg1308 : RowSquare [5,4,1,1] [3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg144

lemma sg1309 : RowSquare [5,4,1,1] [4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg561

lemma sg1310 : RowSquare [5,4,1,1] [4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg562

lemma sg1311 : RowSquare [5,4,1,1] [4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg298

lemma sg1312 : RowSquare [5,4,1,1] [4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg145

lemma sg1313 : RowSquare [5,4,1,1] [4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg142

lemma sg1314 : RowSquare [5,4,1,1] [4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg299

lemma sg1315 : RowSquare [5,4,1,1] [4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg146

lemma sg1316 : RowSquare [5,4,1,1] [4,3,3,1] := by
  exact rowSquare_join (by decide) sg39 sg55

lemma sg1317 : RowSquare [5,4,1,1] [4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg143

lemma sg1318 : RowSquare [5,4,1,1] [4,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg148

lemma sg1319 : RowSquare [5,4,1,1] [4,4,3] := by
  exact rowSquare_join (by decide) sg40 sg55

lemma sg1320 : RowSquare [5,4,1,1] [5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg565

lemma sg1321 : RowSquare [5,4,1,1] [5,3,3] := by
  exact rowSquare_join (by decide) sg41 sg55

lemma sg1322 : RowSquare [5,4,1,1] [5,5,1] := by
  exact rowSquare_join (by decide) sg14 sg148

lemma sg1323 : RowSquare [5,4,2] [2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg306

lemma sg1324 : RowSquare [5,5,1] [3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg166

lemma sg1325 : RowSquare [5,5,1] [4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg166

lemma sg1326 : RowSquare [5,5,1] [5,5,1] := by
  exact rowSquare_join (by decide) sg14 sg171

lemma sg1328 : RowSquare [6,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg112

lemma sg1329 : RowSquare [6,1,1,1,1,1] [2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg111

lemma sg1330 : RowSquare [6,1,1,1,1,1] [2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg265

lemma sg1331 : RowSquare [6,1,1,1,1,1] [2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg530

lemma sg1332 : RowSquare [6,1,1,1,1,1] [2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg909

lemma sg1333 : RowSquare [6,1,1,1,1,1] [3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg888

lemma sg1334 : RowSquare [6,1,1,1,1,1] [3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg889

lemma sg1335 : RowSquare [6,1,1,1,1,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg890

lemma sg1336 : RowSquare [6,1,1,1,1,1] [3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg891

lemma sg1337 : RowSquare [6,1,1,1,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg892

lemma sg1338 : RowSquare [6,1,1,1,1,1] [3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg262

lemma sg1339 : RowSquare [6,1,1,1,1,1] [3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg525

lemma sg1340 : RowSquare [6,1,1,1,1,1] [3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg903

lemma sg1341 : RowSquare [6,1,1,1,1,1] [4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg893

lemma sg1342 : RowSquare [6,1,1,1,1,1] [4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg894

lemma sg1343 : RowSquare [6,1,1,1,1,1] [4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg895

lemma sg1344 : RowSquare [6,1,1,1,1,1] [4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg896

lemma sg1345 : RowSquare [6,1,1,1,1,1] [4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg897

lemma sg1346 : RowSquare [6,1,1,1,1,1] [4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg898

lemma sg1347 : RowSquare [6,1,1,1,1,1] [4,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg899

lemma sg1348 : RowSquare [6,1,1,1,1,1] [4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg520

lemma sg1349 : RowSquare [6,1,1,1,1,1] [4,4,2,1] := by
  exact rowSquare_join (by decide) sg0 sg899

lemma sg1350 : RowSquare [6,1,1,1,1,1] [5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg517

lemma sg1351 : RowSquare [6,1,1,1,1,1] [5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg518

lemma sg1352 : RowSquare [6,1,1,1,1,1] [5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg519

lemma sg1353 : RowSquare [6,1,1,1,1,1] [5,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg520

lemma sg1354 : RowSquare [6,1,1,1,1,1] [5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg900

lemma sg1355 : RowSquare [6,1,1,1,1,1] [5,3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg901

lemma sg1356 : RowSquare [6,1,1,1,1,1] [5,4,1,1] := by
  exact rowSquare_join (by decide) sg0 sg902

lemma sg1357 : RowSquare [6,1,1,1,1,1] [5,4,2] := by
  exact rowSquare_join (by decide) sg0 sg903

lemma sg1358 : RowSquare [6,1,1,1,1,1] [5,5,1] := by
  exact rowSquare_join (by decide) sg0 sg892

lemma sg1359 : RowSquare [6,1,1,1,1,1] [6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg521

lemma sg1360 : RowSquare [6,1,1,1,1,1] [6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg522

lemma sg1361 : RowSquare [6,1,1,1,1,1] [6,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg523

lemma sg1362 : RowSquare [6,1,1,1,1,1] [6,3,1,1] := by
  exact rowSquare_join (by decide) sg2 sg524

lemma sg1363 : RowSquare [6,1,1,1,1,1] [6,3,2] := by
  exact rowSquare_join (by decide) sg2 sg525

lemma sg1364 : RowSquare [6,1,1,1,1,1] [6,4,1] := by
  exact rowSquare_join (by decide) sg0 sg908

lemma sg1365 : RowSquare [6,1,1,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg0 sg909

lemma sg1366 : RowSquare [6,1,1,1,1,1] [7,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg260

lemma sg1367 : RowSquare [6,1,1,1,1,1] [7,2,1,1] := by
  exact rowSquare_join (by decide) sg7 sg261

lemma sg1368 : RowSquare [6,1,1,1,1,1] [7,2,2] := by
  exact rowSquare_join (by decide) sg7 sg262

lemma sg1369 : RowSquare [6,1,1,1,1,1] [7,3,1] := by
  exact rowSquare_join (by decide) sg2 sg529

lemma sg1370 : RowSquare [6,1,1,1,1,1] [7,4] := by
  exact rowSquare_join (by decide) sg2 sg530

lemma sg1371 : RowSquare [6,2,1,1,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg910

lemma sg1372 : RowSquare [6,2,1,1,1] [3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg586

lemma sg1373 : RowSquare [6,2,1,1,1] [3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg912

lemma sg1374 : RowSquare [6,2,1,1,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg312

lemma sg1375 : RowSquare [6,2,1,1,1] [3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg914

lemma sg1376 : RowSquare [6,2,1,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg915

lemma sg1377 : RowSquare [6,2,1,1,1] [3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg313

lemma sg1378 : RowSquare [6,2,1,1,1] [3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg314

lemma sg1379 : RowSquare [6,2,1,1,1] [3,3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg315

lemma sg1380 : RowSquare [6,2,1,1,1] [4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg534

lemma sg1381 : RowSquare [6,2,1,1,1] [4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg312

lemma sg1382 : RowSquare [6,2,1,1,1] [4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg316

lemma sg1383 : RowSquare [6,2,1,1,1] [4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg537

lemma sg1384 : RowSquare [6,2,1,1,1] [4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg313

lemma sg1385 : RowSquare [6,2,1,1,1] [4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg317

lemma sg1386 : RowSquare [6,2,1,1,1] [4,3,2,2] := by
  exact rowSquare_join (by decide) sg5 sg315

lemma sg1387 : RowSquare [6,2,1,1,1] [4,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg318

lemma sg1388 : RowSquare [6,2,1,1,1] [4,4,2,1] := by
  exact rowSquare_join (by decide) sg4 sg319

lemma sg1389 : RowSquare [6,2,1,1,1] [4,4,3] := by
  exact rowSquare_join (by decide) sg4 sg320

lemma sg1390 : RowSquare [6,2,1,1,1] [5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg312

lemma sg1391 : RowSquare [6,2,1,1,1] [5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg316

lemma sg1392 : RowSquare [6,2,1,1,1] [5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg16 sg132

lemma sg1393 : RowSquare [6,2,1,1,1] [5,2,2,2] := by
  exact rowSquare_join (by decide) sg7 sg271

lemma sg1394 : RowSquare [6,2,1,1,1] [5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg132

lemma sg1395 : RowSquare [6,2,1,1,1] [5,3,2,1] := by
  exact rowSquare_join (by decide) sg16 sg133

lemma sg1396 : RowSquare [6,2,1,1,1] [5,3,3] := by
  exact rowSquare_join (by decide) sg16 sg134

lemma sg1397 : RowSquare [6,2,1,1,1] [5,4,1,1] := by
  exact rowSquare_join (by decide) sg17 sg133

lemma sg1398 : RowSquare [6,2,1,1,1] [5,4,2] := by
  exact rowSquare_join (by decide) sg17 sg134

lemma sg1399 : RowSquare [6,2,1,1,1] [5,5,1] := by
  exact rowSquare_join (by decide) sg4 sg324

lemma sg1400 : RowSquare [6,2,1,1,1] [6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg272

lemma sg1401 : RowSquare [6,2,1,1,1] [6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg132

lemma sg1402 : RowSquare [6,2,1,1,1] [6,2,2,1] := by
  exact rowSquare_join (by decide) sg16 sg135

lemma sg1403 : RowSquare [6,2,1,1,1] [6,3,1,1] := by
  exact rowSquare_join (by decide) sg17 sg135

lemma sg1404 : RowSquare [6,2,1,1,1] [6,3,2] := by
  exact rowSquare_join (by decide) sg16 sg136

lemma sg1405 : RowSquare [6,2,1,1,1] [6,4,1] := by
  exact rowSquare_join (by decide) sg16 sg137

lemma sg1406 : RowSquare [6,2,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg17 sg137

lemma sg1407 : RowSquare [6,2,1,1,1] [7,4] := by
  exact rowSquare_join (by decide) sg46 sg52

lemma sg1408 : RowSquare [6,2,2,1] [3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg940

lemma sg1409 : RowSquare [6,2,2,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg9 sg178

lemma sg1410 : RowSquare [6,2,2,1] [3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg942

lemma sg1411 : RowSquare [6,2,2,1] [3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg178

lemma sg1412 : RowSquare [6,2,2,1] [3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg67

lemma sg1413 : RowSquare [6,2,2,1] [3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg32 sg68

lemma sg1414 : RowSquare [6,2,2,1] [4,3,2,2] := by
  exact rowSquare_join (by decide) sg33 sg67

lemma sg1415 : RowSquare [6,2,2,1] [4,3,3,1] := by
  exact rowSquare_join (by decide) sg33 sg68

lemma sg1416 : RowSquare [6,3,1,1] [2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg330

lemma sg1417 : RowSquare [6,3,1,1] [2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg178

lemma sg1418 : RowSquare [6,3,1,1] [3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg330

lemma sg1419 : RowSquare [6,3,1,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg331

lemma sg1420 : RowSquare [6,3,1,1] [3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg179

lemma sg1421 : RowSquare [6,3,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg961

lemma sg1422 : RowSquare [6,3,1,1] [3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg178

lemma sg1423 : RowSquare [6,3,1,1] [3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg332

lemma sg1424 : RowSquare [6,3,1,1] [3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg180

lemma sg1425 : RowSquare [6,3,1,1] [3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg333

lemma sg1426 : RowSquare [6,3,1,1] [3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg181

lemma sg1427 : RowSquare [6,3,1,1] [4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg330

lemma sg1428 : RowSquare [6,3,1,1] [4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg331

lemma sg1429 : RowSquare [6,3,1,1] [4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg142

lemma sg1430 : RowSquare [6,3,1,1] [4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg39 sg66

lemma sg1431 : RowSquare [6,3,1,1] [4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg142

lemma sg1432 : RowSquare [6,3,1,1] [4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg40 sg66

lemma sg1433 : RowSquare [6,3,1,1] [4,3,2,2] := by
  exact rowSquare_join (by decide) sg39 sg67

lemma sg1434 : RowSquare [6,3,1,1] [4,3,3,1] := by
  exact rowSquare_join (by decide) sg39 sg68

lemma sg1435 : RowSquare [6,3,1,1] [4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg143

lemma sg1436 : RowSquare [6,3,1,1] [4,4,2,1] := by
  exact rowSquare_join (by decide) sg40 sg67

lemma sg1437 : RowSquare [6,3,1,1] [4,4,3] := by
  exact rowSquare_join (by decide) sg40 sg68

lemma sg1438 : RowSquare [6,3,1,1] [5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg178

lemma sg1439 : RowSquare [6,3,1,1] [5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg142

lemma sg1440 : RowSquare [6,3,1,1] [5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg41 sg66

lemma sg1441 : RowSquare [6,3,1,1] [5,2,2,2] := by
  exact rowSquare_join (by decide) sg39 sg69

lemma sg1442 : RowSquare [6,3,1,1] [5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg66

lemma sg1443 : RowSquare [6,3,1,1] [5,3,2,1] := by
  exact rowSquare_join (by decide) sg39 sg70

lemma sg1444 : RowSquare [6,3,1,1] [5,3,3] := by
  exact rowSquare_join (by decide) sg45 sg55

lemma sg1445 : RowSquare [6,3,1,1] [5,4,1,1] := by
  exact rowSquare_join (by decide) sg39 sg71

lemma sg1446 : RowSquare [6,3,1,1] [5,4,2] := by
  exact rowSquare_join (by decide) sg40 sg70

lemma sg1447 : RowSquare [6,3,1,1] [5,5,1] := by
  exact rowSquare_join (by decide) sg40 sg71

lemma sg1448 : RowSquare [6,3,1,1] [6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg142

lemma sg1449 : RowSquare [6,3,1,1] [6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg66

lemma sg1450 : RowSquare [6,3,1,1] [6,2,2,1] := by
  exact rowSquare_join (by decide) sg39 sg72

lemma sg1451 : RowSquare [6,3,1,1] [6,3,1,1] := by
  exact rowSquare_join (by decide) sg39 sg73

lemma sg1452 : RowSquare [6,3,1,1] [6,3,2] := by
  exact rowSquare_join (by decide) sg40 sg72

lemma sg1453 : RowSquare [6,3,1,1] [6,4,1] := by
  exact rowSquare_join (by decide) sg40 sg73

lemma sg1454 : RowSquare [6,3,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg42 sg71

lemma sg1455 : RowSquare [6,3,2] [2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg74

lemma sg1456 : RowSquare [6,3,2] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg975

lemma sg1457 : RowSquare [6,3,2] [3,3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg350

lemma sg1458 : RowSquare [6,3,2] [4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg577

lemma sg1459 : RowSquare [6,3,2] [5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg307

lemma sg1460 : RowSquare [6,4,1] [3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg74

lemma sg1461 : RowSquare [6,4,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg982

lemma sg1462 : RowSquare [6,4,1] [3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg74

lemma sg1463 : RowSquare [6,4,1] [3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg194

lemma sg1464 : RowSquare [6,4,1] [3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg32 sg83

lemma sg1465 : RowSquare [6,4,1] [4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg74

lemma sg1466 : RowSquare [6,4,1] [4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg84

lemma sg1467 : RowSquare [6,4,1] [4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg74

lemma sg1468 : RowSquare [6,4,1] [4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg166

lemma sg1469 : RowSquare [6,4,1] [4,4,3] := by
  exact rowSquare_join (by decide) sg40 sg77

lemma sg1470 : RowSquare [6,4,1] [5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg74

lemma sg1471 : RowSquare [6,4,1] [5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg41 sg75

lemma sg1472 : RowSquare [6,4,1] [5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg85

lemma sg1473 : RowSquare [6,4,1] [5,5,1] := by
  exact rowSquare_join (by decide) sg40 sg80

lemma sg1474 : RowSquare [6,4,1] [6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg74

lemma sg1475 : RowSquare [6,4,1] [6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg75

lemma sg1476 : RowSquare [6,4,1] [6,5] := by
  exact rowSquare_join (by decide) sg42 sg80

lemma sg1477 : RowSquare [6,4,1] [7,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg86

lemma sg1498 : RowSquare [7,1,1,1,1] [3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg586

lemma sg1499 : RowSquare [7,1,1,1,1] [3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg998

lemma sg1500 : RowSquare [7,1,1,1,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg999

lemma sg1501 : RowSquare [7,1,1,1,1] [3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1000

lemma sg1502 : RowSquare [7,1,1,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg1001

lemma sg1503 : RowSquare [7,1,1,1,1] [4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg587

lemma sg1504 : RowSquare [7,1,1,1,1] [4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg588

lemma sg1505 : RowSquare [7,1,1,1,1] [4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg589

lemma sg1506 : RowSquare [7,1,1,1,1] [4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg590

lemma sg1507 : RowSquare [7,1,1,1,1] [4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1006

lemma sg1508 : RowSquare [7,1,1,1,1] [4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1007

lemma sg1509 : RowSquare [7,1,1,1,1] [4,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg1008

lemma sg1510 : RowSquare [7,1,1,1,1] [5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg312

lemma sg1511 : RowSquare [7,1,1,1,1] [5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg313

lemma sg1512 : RowSquare [7,1,1,1,1] [5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg595

lemma sg1513 : RowSquare [7,1,1,1,1] [5,3,2,1] := by
  exact rowSquare_join (by decide) sg2 sg596

lemma sg1514 : RowSquare [7,1,1,1,1] [5,4,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1015

lemma sg1515 : RowSquare [7,1,1,1,1] [5,4,2] := by
  exact rowSquare_join (by decide) sg0 sg1016

lemma sg1516 : RowSquare [7,1,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg0 sg1023

lemma sg1517 : RowSquare [7,2,1,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg178

lemma sg1518 : RowSquare [7,2,1,1] [3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1032

lemma sg1519 : RowSquare [7,2,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg1033

lemma sg1520 : RowSquare [7,2,1,1] [3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg178

lemma sg1521 : RowSquare [7,2,1,1] [3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg371

lemma sg1522 : RowSquare [7,2,1,1] [3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg372

lemma sg1523 : RowSquare [7,2,1,1] [3,3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg373

lemma sg1524 : RowSquare [7,2,1,1] [4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg330

lemma sg1525 : RowSquare [7,2,1,1] [4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg178

lemma sg1526 : RowSquare [7,2,1,1] [4,3,3,1] := by
  exact rowSquare_join (by decide) sg16 sg181

lemma sg1527 : RowSquare [7,2,1,1] [4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg180

lemma sg1528 : RowSquare [7,2,1,1] [4,4,2,1] := by
  exact rowSquare_join (by decide) sg17 sg181

lemma sg1529 : RowSquare [7,2,1,1] [4,4,3] := by
  exact rowSquare_join (by decide) sg4 sg378

lemma sg1530 : RowSquare [7,2,1,1] [5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg178

lemma sg1531 : RowSquare [7,2,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg46 sg71

lemma sg1532 : RowSquare [7,2,2] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg87

lemma sg1533 : RowSquare [7,2,2] [3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg88

lemma sg1534 : RowSquare [7,2,2] [3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg32 sg89

lemma sg1535 : RowSquare [7,2,2] [4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg636

lemma sg1536 : RowSquare [7,2,2] [4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1063

lemma sg1537 : RowSquare [7,2,2] [4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg92

lemma sg1538 : RowSquare [7,3,1] [3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg32 sg97

lemma sg1539 : RowSquare [7,3,1] [3,3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg390

lemma sg1540 : RowSquare [7,3,1] [4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg74

lemma sg1541 : RowSquare [7,3,1] [4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg98

lemma sg1542 : RowSquare [7,3,1] [4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg74

lemma sg1543 : RowSquare [7,3,1] [4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg99

lemma sg1544 : RowSquare [7,3,1] [4,3,2,2] := by
  exact rowSquare_join (by decide) sg39 sg88

lemma sg1545 : RowSquare [7,3,1] [4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg194

lemma sg1546 : RowSquare [7,3,1] [4,4,3] := by
  exact rowSquare_join (by decide) sg40 sg89

lemma sg1547 : RowSquare [7,3,1] [5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg47 sg74

lemma sg1548 : RowSquare [7,4] [4,3,3,1] := by
  exact rowSquare_join (by decide) sg39 sg97

lemma sg1549 : RowSquare [7,4] [4,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg228

lemma sg1550 : RowSquare [7,4] [4,4,3] := by
  exact rowSquare_join (by decide) sg40 sg97

lemma sg1551 : RowSquare [7,4] [5,5,1] := by
  exact rowSquare_join (by decide) sg17 sg210

lemma sg1552 : RowSquare [8,1,1,1] [5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg178

lemma sg1553 : RowSquare [8,1,1,1] [5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg371

lemma sg1554 : RowSquare [8,1,1,1] [5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg7 sg372

lemma sg1555 : RowSquare [8,1,1,1] [5,2,2,2] := by
  exact rowSquare_join (by decide) sg7 sg373

lemma sg1556 : RowSquare [8,1,1,1] [6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg179

lemma sg1557 : RowSquare [8,1,1,1] [6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg180

lemma sg1558 : RowSquare [8,1,1,1] [6,2,2,1] := by
  exact rowSquare_join (by decide) sg20 sg181

lemma sg1559 : RowSquare [8,1,1,1] [6,3,1,1] := by
  exact rowSquare_join (by decide) sg7 sg377

lemma sg1560 : RowSquare [8,1,1,1] [6,3,2] := by
  exact rowSquare_join (by decide) sg7 sg378

lemma sg1561 : RowSquare [8,2,1] [5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg104

lemma sg1562 : RowSquare [8,2,1] [5,2,2,2] := by
  exact rowSquare_join (by decide) sg7 sg390

lemma sg1563 : RowSquare [8,2,1] [5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg105

lemma sg1564 : RowSquare [8,2,1] [5,3,2,1] := by
  exact rowSquare_join (by decide) sg45 sg88

lemma sg1565 : RowSquare [8,2,1] [5,3,3] := by
  exact rowSquare_join (by decide) sg45 sg89

lemma sg1566 : RowSquare [8,2,1] [5,4,1,1] := by
  exact rowSquare_join (by decide) sg46 sg88

lemma sg1567 : RowSquare [8,2,1] [5,4,2] := by
  exact rowSquare_join (by decide) sg46 sg89

lemma sg1568 : RowSquare [8,2,1] [6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg74

lemma sg1569 : RowSquare [8,2,1] [6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg106

lemma sg1570 : RowSquare [8,3] [5,3,3] := by
  exact rowSquare_join (by decide) sg45 sg97

lemma sg1571 : RowSquare [8,3] [5,4,2] := by
  exact rowSquare_join (by decide) sg46 sg97

lemma sg1572 : RowSquare [8,3] [5,5,1] := by
  exact rowSquare_join (by decide) sg17 sg228

lemma sg1573 : RowSquare [8,3] [6,4,1] := by
  exact rowSquare_join (by decide) sg40 sg105

lemma sg1574 : RowSquare [8,3] [6,5] := by
  exact rowSquare_join (by decide) sg17 sg230

lemma sg1575 : RowSquare [9,2] [7,2,2] := by
  exact rowSquare_join (by decide) sg45 sg104

lemma sg1576 : RowSquare [9,2] [7,4] := by
  exact rowSquare_join (by decide) sg46 sg105

lemma sg1577 : RowSquare [2,2,1,1,1,1,1,1,1,1] [8,4] := by
  exact rowSquare_join (by decide) sg105 sg105

lemma sg1578 : RowSquare [2,2,1,1,1,1,1,1,1,1] [9,3] := by
  exact rowSquare_join (by decide) sg105 sg106

lemma sg1579 : RowSquare [2,2,1,1,1,1,1,1,1,1] [10,2] := by
  exact rowSquare_join (by decide) sg105 sg107

lemma sg1580 : RowSquare [2,2,1,1,1,1,1,1,1,1] [11,1] := by
  exact rowSquare_join (by decide) sg106 sg107

lemma sg1581 : RowSquare [2,2,2,1,1,1,1,1,1] [6,6] := by
  exact rowSquare_join (by decide) sg17 sg424

lemma sg1582 : RowSquare [2,2,2,1,1,1,1,1,1] [7,5] := by
  exact rowSquare_join (by decide) sg46 sg230

lemma sg1583 : RowSquare [3,2,1,1,1,1,1,1,1] [6,3,3] := by
  exact rowSquare_join (by decide) sg89 sg104

lemma sg1584 : RowSquare [3,2,1,1,1,1,1,1,1] [7,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg108

lemma sg1585 : RowSquare [3,2,1,1,1,1,1,1,1] [7,2,1,1,1] := by
  exact rowSquare_join (by decide) sg87 sg106

lemma sg1586 : RowSquare [3,2,2,1,1,1,1,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg97 sg89

lemma sg1587 : RowSquare [3,2,2,2,1,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg390

lemma sg1588 : RowSquare [3,2,2,2,2,1] [3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg356

lemma sg1589 : RowSquare [3,2,2,2,2,1] [3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg83

lemma sg1590 : RowSquare [3,2,2,2,2,1] [3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg357

lemma sg1591 : RowSquare [3,2,2,2,2,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg358

lemma sg1592 : RowSquare [3,3,1,1,1,1,1,1] [4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg87 sg87

lemma sg1593 : RowSquare [3,3,1,1,1,1,1,1] [4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg87 sg88

lemma sg1594 : RowSquare [3,3,1,1,1,1,1,1] [4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg87 sg89

lemma sg1595 : RowSquare [3,3,1,1,1,1,1,1] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg88 sg88

lemma sg1596 : RowSquare [3,3,1,1,1,1,1,1] [4,4,3,1] := by
  exact rowSquare_join (by decide) sg88 sg89

lemma sg1597 : RowSquare [3,3,1,1,1,1,1,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg89 sg89

lemma sg1598 : RowSquare [3,3,1,1,1,1,1,1] [5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg636

lemma sg1599 : RowSquare [3,3,1,1,1,1,1,1] [5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg87 sg90

lemma sg1600 : RowSquare [3,3,1,1,1,1,1,1] [5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1063

lemma sg1601 : RowSquare [3,3,1,1,1,1,1,1] [5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg87 sg91

lemma sg1602 : RowSquare [3,3,1,1,1,1,1,1] [5,3,2,2] := by
  exact rowSquare_join (by decide) sg88 sg90

lemma sg1603 : RowSquare [3,3,1,1,1,1,1,1] [5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg87 sg92

lemma sg1604 : RowSquare [3,3,1,1,1,1,1,1] [6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg348

lemma sg1605 : RowSquare [3,3,1,1,1,1,1,1] [6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg87 sg94

lemma sg1606 : RowSquare [3,3,1,1,1,1,1,1] [6,6] := by
  exact rowSquare_join (by decide) sg92 sg92

lemma sg1607 : RowSquare [3,3,1,1,1,1,1,1] [7,2,1,1,1] := by
  exact rowSquare_join (by decide) sg87 sg95

lemma sg1608 : RowSquare [3,3,1,1,1,1,1,1] [8,1,1,1,1] := by
  exact rowSquare_join (by decide) sg87 sg96

lemma sg1609 : RowSquare [3,3,2,1,1,1,1] [5,5,2] := by
  exact rowSquare_join (by decide) sg89 sg80

lemma sg1610 : RowSquare [3,3,2,1,1,1,1] [6,2,2,2] := by
  exact rowSquare_join (by decide) sg90 sg78

lemma sg1611 : RowSquare [3,3,2,1,1,1,1] [6,6] := by
  exact rowSquare_join (by decide) sg92 sg80

lemma sg1612 : RowSquare [3,3,2,1,1,1,1] [7,5] := by
  exact rowSquare_join (by decide) sg92 sg81

lemma sg1613 : RowSquare [3,3,2,1,1,1,1] [8,2,2] := by
  exact rowSquare_join (by decide) sg3 sg432

lemma sg1614 : RowSquare [3,3,2,1,1,1,1] [9,3] := by
  exact rowSquare_join (by decide) sg3 sg437

lemma sg1616 : RowSquare [3,3,2,2,1,1] [2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg74

lemma sg1617 : RowSquare [3,3,2,2,2] [6,6] := by
  exact rowSquare_join (by decide) sg14 sg311

lemma sg1618 : RowSquare [3,3,3,1,1,1] [3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg154

lemma sg1619 : RowSquare [3,3,3,2,1] [2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg516

lemma sg1620 : RowSquare [4,1,1,1,1,1,1,1,1] [8,4] := by
  exact rowSquare_join (by decide) sg20 sg383

lemma sg1621 : RowSquare [4,2,1,1,1,1,1,1] [5,4,3] := by
  exact rowSquare_join (by decide) sg16 sg378

lemma sg1622 : RowSquare [4,2,1,1,1,1,1,1] [5,5,1,1] := by
  exact rowSquare_join (by decide) sg17 sg377

lemma sg1623 : RowSquare [4,2,1,1,1,1,1,1] [5,5,2] := by
  exact rowSquare_join (by decide) sg17 sg378

lemma sg1624 : RowSquare [4,2,1,1,1,1,1,1] [6,5,1] := by
  exact rowSquare_join (by decide) sg46 sg185

lemma sg1625 : RowSquare [4,2,1,1,1,1,1,1] [6,6] := by
  exact rowSquare_join (by decide) sg17 sg383

lemma sg1626 : RowSquare [4,2,2,1,1,1,1] [3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg330

lemma sg1627 : RowSquare [4,2,2,1,1,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg373

lemma sg1628 : RowSquare [4,2,2,2,1,1] [2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg330

lemma sg1629 : RowSquare [4,2,2,2,1,1] [3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg563

lemma sg1630 : RowSquare [4,2,2,2,1,1] [3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg333

lemma sg1631 : RowSquare [4,2,2,2,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg334

lemma sg1632 : RowSquare [4,3,1,1,1,1,1] [2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg178

lemma sg1633 : RowSquare [4,3,1,1,1,1,1] [3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg178

lemma sg1634 : RowSquare [4,3,1,1,1,1,1] [3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg179

lemma sg1635 : RowSquare [4,3,1,1,1,1,1] [3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg34 sg178

lemma sg1636 : RowSquare [4,3,1,1,1,1,1] [3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg180

lemma sg1637 : RowSquare [4,3,1,1,1,1,1] [4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg940

lemma sg1638 : RowSquare [4,3,1,1,1,1,1] [4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg35 sg178

lemma sg1639 : RowSquare [4,3,1,1,1,1,1] [4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg36 sg178

lemma sg1640 : RowSquare [4,3,1,1,1,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg371

lemma sg1641 : RowSquare [4,3,1,1,1,1,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg89 sg68

lemma sg1642 : RowSquare [4,3,1,1,1,1,1] [5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg548

lemma sg1643 : RowSquare [4,3,1,1,1,1,1] [5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg37 sg178

lemma sg1644 : RowSquare [4,3,1,1,1,1,1] [6,6] := by
  exact rowSquare_join (by decide) sg92 sg71

lemma sg1645 : RowSquare [4,3,2,1,1,1] [3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg178

lemma sg1646 : RowSquare [4,3,2,1,1,1] [3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg330

lemma sg1647 : RowSquare [4,3,2,1,1,1] [3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg143

lemma sg1648 : RowSquare [4,3,3,1,1] [3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1233

lemma sg1649 : RowSquare [4,4,1,1,1,1] [4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg23 sg178

lemma sg1651 : RowSquare [4,4,2,2] [2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg60 sg61

lemma sg1652 : RowSquare [4,4,2,2] [2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg59 sg61

lemma sg1653 : RowSquare [4,4,2,2] [2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg59 sg60

lemma sg1654 : RowSquare [4,4,2,2] [2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg257

lemma sg1655 : RowSquare [4,4,2,2] [3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg58 sg61

lemma sg1656 : RowSquare [4,4,2,2] [3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg57 sg61

lemma sg1657 : RowSquare [4,4,2,2] [4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg56 sg61

lemma sg1658 : RowSquare [4,4,2,2] [4,4,4] := by
  exact rowSquare_join (by decide) sg55 sg55

lemma sg1659 : RowSquare [5,1,1,1,1,1,1,1] [4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg1001

lemma sg1660 : RowSquare [5,1,1,1,1,1,1,1] [5,3,2,2] := by
  exact rowSquare_join (by decide) sg2 sg1008

lemma sg1661 : RowSquare [5,1,1,1,1,1,1,1] [6,4,2] := by
  exact rowSquare_join (by decide) sg2 sg1016

lemma sg1662 : RowSquare [5,1,1,1,1,1,1,1] [7,5] := by
  exact rowSquare_join (by decide) sg2 sg1023

end UniversalTensorSquare
end
end

end OAI
