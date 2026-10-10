import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupLocalLeaves
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupLeaves1
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupLeaves2

namespace OAI

/-! Semigroup Nodes 0. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg22 : RowSquare [2,1,1,1] [3,1,1] := by
  exact rowSquare_join (by decide) sg2 sg4

lemma sg23 : RowSquare [2,1,1,1] [3,2] := by
  exact rowSquare_join (by decide) sg0 sg17

lemma sg24 : RowSquare [2,1,1,1] [4,1] := by
  exact rowSquare_join (by decide) sg2 sg5

lemma sg45 : RowSquare [4,1] [3,1,1] := by
  exact rowSquare_join (by decide) sg2 sg4

lemma sg46 : RowSquare [4,1] [3,2] := by
  exact rowSquare_join (by decide) sg0 sg17

lemma sg47 : RowSquare [4,1] [4,1] := by
  exact rowSquare_join (by decide) sg2 sg5

lemma sg51 : RowSquare [2,1,1,1,1] [4,1,1] := by
  exact rowSquare_join (by decide) sg4 sg7

lemma sg52 : RowSquare [2,1,1,1,1] [4,2] := by
  exact rowSquare_join (by decide) sg2 sg17

lemma sg53 : RowSquare [2,1,1,1,1] [5,1] := by
  exact rowSquare_join (by decide) sg5 sg7

lemma sg63 : RowSquare [2,2,2] [3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg13

lemma sg66 : RowSquare [3,1,1,1] [2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg32

lemma sg69 : RowSquare [3,1,1,1] [3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg33

lemma sg70 : RowSquare [3,1,1,1] [3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg34

lemma sg72 : RowSquare [3,1,1,1] [4,1,1] := by
  exact rowSquare_join (by decide) sg0 sg22

lemma sg73 : RowSquare [3,1,1,1] [4,2] := by
  exact rowSquare_join (by decide) sg0 sg23

lemma sg84 : RowSquare [3,3] [3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg13

lemma sg87 : RowSquare [4,1,1] [2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg32

lemma sg90 : RowSquare [4,1,1] [3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg33

lemma sg91 : RowSquare [4,1,1] [3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg34

lemma sg93 : RowSquare [4,1,1] [4,1,1] := by
  exact rowSquare_join (by decide) sg2 sg9

lemma sg94 : RowSquare [4,1,1] [4,2] := by
  exact rowSquare_join (by decide) sg2 sg10

lemma sg95 : RowSquare [4,1,1] [5,1] := by
  exact rowSquare_join (by decide) sg2 sg11

lemma sg104 : RowSquare [5,1] [4,1,1] := by
  exact rowSquare_join (by decide) sg4 sg7

lemma sg105 : RowSquare [5,1] [4,2] := by
  exact rowSquare_join (by decide) sg2 sg17

lemma sg106 : RowSquare [5,1] [5,1] := by
  exact rowSquare_join (by decide) sg5 sg7

lemma sg110 : RowSquare [2,1,1,1,1,1] [5,1,1] := by
  exact rowSquare_join (by decide) sg4 sg20

lemma sg111 : RowSquare [2,1,1,1,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg7 sg17

lemma sg112 : RowSquare [2,1,1,1,1,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg20

lemma sg114 : RowSquare [2,2,1,1,1] [3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg16

lemma sg115 : RowSquare [2,2,1,1,1] [3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg17

lemma sg116 : RowSquare [2,2,1,1,1] [4,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg13

lemma sg117 : RowSquare [2,2,1,1,1] [4,2,1] := by
  exact rowSquare_join (by decide) sg4 sg18

lemma sg118 : RowSquare [2,2,1,1,1] [4,3] := by
  exact rowSquare_join (by decide) sg5 sg17

lemma sg119 : RowSquare [2,2,1,1,1] [5,1,1] := by
  exact rowSquare_join (by decide) sg4 sg19

lemma sg120 : RowSquare [2,2,1,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg5 sg18

lemma sg121 : RowSquare [2,2,1,1,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg19

lemma sg132 : RowSquare [3,1,1,1,1] [3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg32

lemma sg133 : RowSquare [3,1,1,1,1] [3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg88

lemma sg134 : RowSquare [3,1,1,1,1] [3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg89

lemma sg135 : RowSquare [3,1,1,1,1] [4,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg33

lemma sg136 : RowSquare [3,1,1,1,1] [4,2,1] := by
  exact rowSquare_join (by decide) sg2 sg34

lemma sg137 : RowSquare [3,1,1,1,1] [4,3] := by
  exact rowSquare_join (by decide) sg0 sg92

lemma sg138 : RowSquare [3,1,1,1,1] [5,1,1] := by
  exact rowSquare_join (by decide) sg0 sg51

lemma sg139 : RowSquare [3,1,1,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg0 sg52

lemma sg140 : RowSquare [3,1,1,1,1] [6,1] := by
  exact rowSquare_join (by decide) sg0 sg53

lemma sg142 : RowSquare [3,2,1,1] [2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg74

lemma sg145 : RowSquare [3,2,1,1] [3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg32

lemma sg146 : RowSquare [3,2,1,1] [3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg76

lemma sg147 : RowSquare [3,2,1,1] [3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg55

lemma sg148 : RowSquare [3,2,1,1] [3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg10

lemma sg149 : RowSquare [3,2,1,1] [4,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg56

lemma sg150 : RowSquare [3,2,1,1] [4,2,1] := by
  exact rowSquare_join (by decide) sg0 sg57

lemma sg151 : RowSquare [3,2,1,1] [4,3] := by
  exact rowSquare_join (by decide) sg5 sg10

lemma sg152 : RowSquare [3,2,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg1 sg23

lemma sg153 : RowSquare [3,2,1,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg8

lemma sg159 : RowSquare [3,2,2] [3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg62

lemma sg161 : RowSquare [3,2,2] [4,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg63

lemma sg162 : RowSquare [3,2,2] [4,2,1] := by
  exact rowSquare_join (by decide) sg1 sg27

lemma sg164 : RowSquare [3,2,2] [5,2] := by
  exact rowSquare_join (by decide) sg3 sg10

lemma sg170 : RowSquare [3,3,1] [3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg62

lemma sg172 : RowSquare [3,3,1] [4,1,1,1] := by
  exact rowSquare_join (by decide) sg3 sg13

lemma sg173 : RowSquare [3,3,1] [4,2,1] := by
  exact rowSquare_join (by decide) sg1 sg27

lemma sg175 : RowSquare [3,3,1] [5,1,1] := by
  exact rowSquare_join (by decide) sg1 sg28

lemma sg176 : RowSquare [3,3,1] [5,2] := by
  exact rowSquare_join (by decide) sg3 sg14

lemma sg177 : RowSquare [3,3,1] [6,1] := by
  exact rowSquare_join (by decide) sg1 sg30

lemma sg193 : RowSquare [4,2,1] [2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg74

lemma sg196 : RowSquare [4,2,1] [3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg32

lemma sg197 : RowSquare [4,2,1] [3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg76

lemma sg198 : RowSquare [4,2,1] [3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg9

lemma sg199 : RowSquare [4,2,1] [3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg10

lemma sg200 : RowSquare [4,2,1] [4,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg26

lemma sg201 : RowSquare [4,2,1] [4,2,1] := by
  exact rowSquare_join (by decide) sg4 sg11

lemma sg202 : RowSquare [4,2,1] [4,3] := by
  exact rowSquare_join (by decide) sg5 sg10

lemma sg203 : RowSquare [4,2,1] [5,1,1] := by
  exact rowSquare_join (by decide) sg4 sg12

lemma sg204 : RowSquare [4,2,1] [5,2] := by
  exact rowSquare_join (by decide) sg5 sg11

lemma sg205 : RowSquare [4,2,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg12

lemma sg218 : RowSquare [5,1,1] [3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg32

lemma sg219 : RowSquare [5,1,1] [3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg88

lemma sg220 : RowSquare [5,1,1] [3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg89

lemma sg221 : RowSquare [5,1,1] [4,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg33

lemma sg222 : RowSquare [5,1,1] [4,2,1] := by
  exact rowSquare_join (by decide) sg2 sg34

lemma sg223 : RowSquare [5,1,1] [4,3] := by
  exact rowSquare_join (by decide) sg0 sg92

lemma sg224 : RowSquare [5,1,1] [5,1,1] := by
  exact rowSquare_join (by decide) sg7 sg9

lemma sg225 : RowSquare [5,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg7 sg10

lemma sg227 : RowSquare [5,2] [3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg16

lemma sg228 : RowSquare [5,2] [3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg17

lemma sg229 : RowSquare [5,2] [4,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg13

lemma sg230 : RowSquare [5,2] [4,3] := by
  exact rowSquare_join (by decide) sg5 sg17

lemma sg231 : RowSquare [6,1] [5,1,1] := by
  exact rowSquare_join (by decide) sg4 sg20

lemma sg232 : RowSquare [6,1] [5,2] := by
  exact rowSquare_join (by decide) sg7 sg17

lemma sg233 : RowSquare [6,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg20

lemma sg236 : RowSquare [2,1,1,1,1,1,1] [6,2] := by
  exact rowSquare_join (by decide) sg17 sg20

lemma sg237 : RowSquare [2,1,1,1,1,1,1] [7,1] := by
  exact rowSquare_join (by decide) sg18 sg20

lemma sg239 : RowSquare [2,2,1,1,1,1] [4,2,2] := by
  exact rowSquare_join (by decide) sg16 sg16

lemma sg240 : RowSquare [2,2,1,1,1,1] [4,3,1] := by
  exact rowSquare_join (by decide) sg16 sg17

lemma sg241 : RowSquare [2,2,1,1,1,1] [4,4] := by
  exact rowSquare_join (by decide) sg17 sg17

lemma sg242 : RowSquare [2,2,1,1,1,1] [5,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg20

lemma sg243 : RowSquare [2,2,1,1,1,1] [5,2,1] := by
  exact rowSquare_join (by decide) sg16 sg18

lemma sg244 : RowSquare [2,2,1,1,1,1] [5,3] := by
  exact rowSquare_join (by decide) sg17 sg18

lemma sg245 : RowSquare [2,2,1,1,1,1] [6,1,1] := by
  exact rowSquare_join (by decide) sg16 sg19

lemma sg246 : RowSquare [2,2,1,1,1,1] [6,2] := by
  exact rowSquare_join (by decide) sg17 sg19

lemma sg247 : RowSquare [2,2,1,1,1,1] [7,1] := by
  exact rowSquare_join (by decide) sg18 sg19

lemma sg250 : RowSquare [2,2,2,1,1] [3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg17

lemma sg252 : RowSquare [2,2,2,1,1] [4,4] := by
  exact rowSquare_join (by decide) sg17 sg14

lemma sg254 : RowSquare [2,2,2,2] [2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13

lemma sg255 : RowSquare [2,2,2,2] [3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14

lemma sg258 : RowSquare [2,2,2,2] [5,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg15

lemma sg260 : RowSquare [3,1,1,1,1,1] [4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg32

lemma sg261 : RowSquare [3,1,1,1,1,1] [4,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg88

lemma sg262 : RowSquare [3,1,1,1,1,1] [4,2,2] := by
  exact rowSquare_join (by decide) sg2 sg89

lemma sg263 : RowSquare [3,1,1,1,1,1] [5,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg33

lemma sg264 : RowSquare [3,1,1,1,1,1] [5,2,1] := by
  exact rowSquare_join (by decide) sg7 sg34

lemma sg265 : RowSquare [3,1,1,1,1,1] [5,3] := by
  exact rowSquare_join (by decide) sg2 sg92

lemma sg266 : RowSquare [3,1,1,1,1,1] [6,1,1] := by
  exact rowSquare_join (by decide) sg0 sg110

lemma sg267 : RowSquare [3,1,1,1,1,1] [6,2] := by
  exact rowSquare_join (by decide) sg0 sg111

lemma sg268 : RowSquare [3,1,1,1,1,1] [7,1] := by
  exact rowSquare_join (by decide) sg0 sg112

lemma sg270 : RowSquare [3,2,1,1,1] [2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg32

lemma sg272 : RowSquare [3,2,1,1,1] [3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg74

lemma sg273 : RowSquare [3,2,1,1,1] [3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg32

lemma sg274 : RowSquare [3,2,1,1,1] [3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg33

lemma sg276 : RowSquare [3,2,1,1,1] [3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg34

lemma sg277 : RowSquare [3,2,1,1,1] [4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg32

lemma sg278 : RowSquare [3,2,1,1,1] [4,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg33

lemma sg279 : RowSquare [3,2,1,1,1] [4,2,2] := by
  exact rowSquare_join (by decide) sg0 sg114

lemma sg280 : RowSquare [3,2,1,1,1] [4,3,1] := by
  exact rowSquare_join (by decide) sg0 sg115

lemma sg281 : RowSquare [3,2,1,1,1] [4,4] := by
  exact rowSquare_join (by decide) sg17 sg10

lemma sg282 : RowSquare [3,2,1,1,1] [5,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg116

lemma sg283 : RowSquare [3,2,1,1,1] [5,2,1] := by
  exact rowSquare_join (by decide) sg0 sg117

lemma sg284 : RowSquare [3,2,1,1,1] [5,3] := by
  exact rowSquare_join (by decide) sg0 sg118

lemma sg288 : RowSquare [3,2,2,1] [3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg74

lemma sg289 : RowSquare [3,2,2,1] [3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg166

lemma sg290 : RowSquare [3,2,2,1] [3,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg123

lemma sg291 : RowSquare [3,2,2,1] [3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10

lemma sg292 : RowSquare [3,2,2,1] [3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg27

lemma sg293 : RowSquare [3,2,2,1] [4,3,1] := by
  exact rowSquare_join (by decide) sg0 sg125

lemma sg294 : RowSquare [3,2,2,1] [4,4] := by
  exact rowSquare_join (by decide) sg14 sg10

lemma sg298 : RowSquare [3,3,1,1] [3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg154

lemma sg299 : RowSquare [3,3,1,1] [3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg155

lemma sg302 : RowSquare [3,3,1,1] [4,4] := by
  exact rowSquare_join (by decide) sg10 sg10

lemma sg303 : RowSquare [3,3,1,1] [5,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg8

lemma sg304 : RowSquare [3,3,1,1] [5,2,1] := by
  exact rowSquare_join (by decide) sg1 sg57

lemma sg305 : RowSquare [3,3,1,1] [5,3] := by
  exact rowSquare_join (by decide) sg10 sg11

lemma sg307 : RowSquare [3,3,2] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3 sg30

lemma sg308 : RowSquare [3,3,2] [2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3 sg29

lemma sg312 : RowSquare [4,1,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg316 : RowSquare [4,1,1,1,1] [3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg179

lemma sg317 : RowSquare [4,1,1,1,1] [3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg180

lemma sg318 : RowSquare [4,1,1,1,1] [3,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg181

lemma sg321 : RowSquare [4,1,1,1,1] [4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg132

lemma sg322 : RowSquare [4,1,1,1,1] [4,2,2] := by
  exact rowSquare_join (by decide) sg0 sg134

lemma sg323 : RowSquare [4,1,1,1,1] [4,3,1] := by
  exact rowSquare_join (by decide) sg0 sg185

lemma sg325 : RowSquare [4,1,1,1,1] [5,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg135

lemma sg326 : RowSquare [4,1,1,1,1] [5,2,1] := by
  exact rowSquare_join (by decide) sg0 sg136

lemma sg327 : RowSquare [4,1,1,1,1] [5,3] := by
  exact rowSquare_join (by decide) sg0 sg137

lemma sg328 : RowSquare [4,1,1,1,1] [6,1,1] := by
  exact rowSquare_join (by decide) sg2 sg51

lemma sg329 : RowSquare [4,1,1,1,1] [6,2] := by
  exact rowSquare_join (by decide) sg2 sg52

lemma sg351 : RowSquare [4,2,2] [3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg154

lemma sg354 : RowSquare [4,2,2] [4,4] := by
  exact rowSquare_join (by decide) sg10 sg10

lemma sg355 : RowSquare [4,2,2] [5,3] := by
  exact rowSquare_join (by decide) sg10 sg11

lemma sg359 : RowSquare [4,3,1] [3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg74

lemma sg360 : RowSquare [4,3,1] [3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10

lemma sg361 : RowSquare [4,3,1] [3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg27

lemma sg362 : RowSquare [4,3,1] [4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg75

lemma sg363 : RowSquare [4,3,1] [4,4] := by
  exact rowSquare_join (by decide) sg14 sg10

lemma sg364 : RowSquare [4,4] [2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13

lemma sg365 : RowSquare [4,4] [3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14

lemma sg368 : RowSquare [4,4] [5,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg15

lemma sg370 : RowSquare [5,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg374 : RowSquare [5,1,1,1] [3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg179

lemma sg375 : RowSquare [5,1,1,1] [3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg180

lemma sg376 : RowSquare [5,1,1,1] [3,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg181

lemma sg379 : RowSquare [5,1,1,1] [4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg66

lemma sg380 : RowSquare [5,1,1,1] [4,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg67

lemma sg381 : RowSquare [5,1,1,1] [4,2,2] := by
  exact rowSquare_join (by decide) sg2 sg68

lemma sg382 : RowSquare [5,1,1,1] [4,3,1] := by
  exact rowSquare_join (by decide) sg0 sg185

lemma sg384 : RowSquare [5,1,1,1] [5,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg69

lemma sg385 : RowSquare [5,1,1,1] [5,2,1] := by
  exact rowSquare_join (by decide) sg2 sg70

lemma sg386 : RowSquare [5,1,1,1] [5,3] := by
  exact rowSquare_join (by decide) sg2 sg71

lemma sg387 : RowSquare [5,1,1,1] [6,1,1] := by
  exact rowSquare_join (by decide) sg7 sg22

lemma sg388 : RowSquare [5,1,1,1] [6,2] := by
  exact rowSquare_join (by decide) sg7 sg23

lemma sg389 : RowSquare [5,2,1] [2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg32

lemma sg391 : RowSquare [5,2,1] [3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg74

lemma sg392 : RowSquare [5,2,1] [3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg32

lemma sg393 : RowSquare [5,2,1] [3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg33

lemma sg395 : RowSquare [5,2,1] [3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg34

lemma sg396 : RowSquare [5,2,1] [4,4] := by
  exact rowSquare_join (by decide) sg17 sg10

lemma sg397 : RowSquare [5,2,1] [5,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg26

lemma sg398 : RowSquare [5,2,1] [5,2,1] := by
  exact rowSquare_join (by decide) sg16 sg11

lemma sg399 : RowSquare [5,2,1] [5,3] := by
  exact rowSquare_join (by decide) sg17 sg11

lemma sg400 : RowSquare [5,2,1] [7,1] := by
  exact rowSquare_join (by decide) sg18 sg12

lemma sg402 : RowSquare [5,3] [3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg17

lemma sg407 : RowSquare [5,3] [4,4] := by
  exact rowSquare_join (by decide) sg17 sg14

lemma sg413 : RowSquare [6,1,1] [4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg32

lemma sg414 : RowSquare [6,1,1] [4,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg88

lemma sg415 : RowSquare [6,1,1] [4,2,2] := by
  exact rowSquare_join (by decide) sg2 sg89

lemma sg416 : RowSquare [6,1,1] [5,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg33

lemma sg417 : RowSquare [6,1,1] [5,2,1] := by
  exact rowSquare_join (by decide) sg7 sg34

lemma sg418 : RowSquare [6,1,1] [5,3] := by
  exact rowSquare_join (by decide) sg2 sg92

lemma sg419 : RowSquare [6,1,1] [6,1,1] := by
  exact rowSquare_join (by decide) sg9 sg20

lemma sg420 : RowSquare [6,1,1] [6,2] := by
  exact rowSquare_join (by decide) sg10 sg20

lemma sg422 : RowSquare [6,2] [4,2,2] := by
  exact rowSquare_join (by decide) sg16 sg16

lemma sg423 : RowSquare [6,2] [4,3,1] := by
  exact rowSquare_join (by decide) sg16 sg17

lemma sg424 : RowSquare [6,2] [4,4] := by
  exact rowSquare_join (by decide) sg17 sg17

lemma sg425 : RowSquare [7,1] [6,2] := by
  exact rowSquare_join (by decide) sg17 sg20

lemma sg428 : RowSquare [2,1,1,1,1,1,1,1] [7,1,1] := by
  exact rowSquare_join (by decide) sg16 sg49

lemma sg429 : RowSquare [2,1,1,1,1,1,1,1] [7,2] := by
  exact rowSquare_join (by decide) sg17 sg49

lemma sg430 : RowSquare [2,1,1,1,1,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg18 sg49

lemma sg432 : RowSquare [2,2,1,1,1,1,1] [5,2,2] := by
  exact rowSquare_join (by decide) sg16 sg45

lemma sg433 : RowSquare [2,2,1,1,1,1,1] [5,3,1] := by
  exact rowSquare_join (by decide) sg16 sg46

lemma sg434 : RowSquare [2,2,1,1,1,1,1] [5,4] := by
  exact rowSquare_join (by decide) sg17 sg46

lemma sg435 : RowSquare [2,2,1,1,1,1,1] [6,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg49

lemma sg436 : RowSquare [2,2,1,1,1,1,1] [6,2,1] := by
  exact rowSquare_join (by decide) sg16 sg47

lemma sg437 : RowSquare [2,2,1,1,1,1,1] [6,3] := by
  exact rowSquare_join (by decide) sg17 sg47

lemma sg438 : RowSquare [2,2,1,1,1,1,1] [7,2] := by
  exact rowSquare_join (by decide) sg17 sg48

lemma sg439 : RowSquare [2,2,1,1,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg18 sg48

lemma sg440 : RowSquare [2,2,2,1,1,1] [3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg97

lemma sg441 : RowSquare [2,2,2,1,1,1] [4,4,1] := by
  exact rowSquare_join (by decide) sg17 sg40

lemma sg442 : RowSquare [2,2,2,1,1,1] [5,4] := by
  exact rowSquare_join (by decide) sg17 sg42

lemma sg443 : RowSquare [2,2,2,1,1,1] [6,3] := by
  exact rowSquare_join (by decide) sg17 sg43

lemma sg444 : RowSquare [2,2,2,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg18 sg44

lemma sg447 : RowSquare [3,1,1,1,1,1,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg32

lemma sg448 : RowSquare [3,1,1,1,1,1,1] [5,2,1,1] := by
  exact rowSquare_join (by decide) sg7 sg88

lemma sg449 : RowSquare [3,1,1,1,1,1,1] [5,2,2] := by
  exact rowSquare_join (by decide) sg7 sg89

lemma sg450 : RowSquare [3,1,1,1,1,1,1] [6,2,1] := by
  exact rowSquare_join (by decide) sg20 sg34

lemma sg451 : RowSquare [3,1,1,1,1,1,1] [6,3] := by
  exact rowSquare_join (by decide) sg7 sg92

lemma sg452 : RowSquare [3,1,1,1,1,1,1] [7,2] := by
  exact rowSquare_join (by decide) sg0 sg236

lemma sg453 : RowSquare [3,1,1,1,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg0 sg237

lemma sg455 : RowSquare [3,2,1,1,1,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg16 sg32

lemma sg456 : RowSquare [3,2,1,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg390

lemma sg457 : RowSquare [3,2,1,1,1,1] [3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg32

lemma sg458 : RowSquare [3,2,1,1,1,1] [3,3,2,1] := by
  exact rowSquare_join (by decide) sg4 sg88

lemma sg459 : RowSquare [3,2,1,1,1,1] [3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg89

lemma sg460 : RowSquare [3,2,1,1,1,1] [4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg74

lemma sg461 : RowSquare [3,2,1,1,1,1] [4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg32

lemma sg462 : RowSquare [3,2,1,1,1,1] [4,2,2,1] := by
  exact rowSquare_join (by decide) sg16 sg33

lemma sg463 : RowSquare [3,2,1,1,1,1] [4,3,1,1] := by
  exact rowSquare_join (by decide) sg17 sg33

lemma sg464 : RowSquare [3,2,1,1,1,1] [4,3,2] := by
  exact rowSquare_join (by decide) sg16 sg34

lemma sg465 : RowSquare [3,2,1,1,1,1] [4,4,1] := by
  exact rowSquare_join (by decide) sg17 sg34

lemma sg466 : RowSquare [3,2,1,1,1,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg32

lemma sg467 : RowSquare [3,2,1,1,1,1] [5,2,1,1] := by
  exact rowSquare_join (by decide) sg18 sg33

lemma sg468 : RowSquare [3,2,1,1,1,1] [5,2,2] := by
  exact rowSquare_join (by decide) sg0 sg239

lemma sg469 : RowSquare [3,2,1,1,1,1] [5,3,1] := by
  exact rowSquare_join (by decide) sg0 sg240

lemma sg470 : RowSquare [3,2,1,1,1,1] [5,4] := by
  exact rowSquare_join (by decide) sg0 sg241

lemma sg471 : RowSquare [3,2,1,1,1,1] [6,3] := by
  exact rowSquare_join (by decide) sg0 sg244

lemma sg472 : RowSquare [3,2,1,1,1,1] [7,2] := by
  exact rowSquare_join (by decide) sg1 sg111

lemma sg473 : RowSquare [3,2,1,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg5 sg50

lemma sg475 : RowSquare [3,2,2,1,1] [2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg74

lemma sg476 : RowSquare [3,2,2,1,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg32

lemma sg477 : RowSquare [3,2,2,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg33

lemma sg478 : RowSquare [3,2,2,1,1] [3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg32

lemma sg479 : RowSquare [3,2,2,1,1] [3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg77

lemma sg485 : RowSquare [3,2,2,2] [4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg165

lemma sg486 : RowSquare [3,2,2,2] [4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg166

lemma sg488 : RowSquare [3,2,2,2] [4,4,1] := by
  exact rowSquare_join (by decide) sg14 sg27

lemma sg491 : RowSquare [3,3,1,1,1] [3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg348

lemma sg492 : RowSquare [3,3,1,1,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg9 sg32

lemma sg493 : RowSquare [3,3,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg350

lemma sg494 : RowSquare [3,3,1,1,1] [3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg32

lemma sg497 : RowSquare [3,3,1,1,1] [4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg154

lemma sg498 : RowSquare [3,3,1,1,1] [4,2,2,1] := by
  exact rowSquare_join (by decide) sg9 sg33

lemma sg499 : RowSquare [3,3,1,1,1] [4,3,2] := by
  exact rowSquare_join (by decide) sg9 sg34

lemma sg500 : RowSquare [3,3,1,1,1] [4,4,1] := by
  exact rowSquare_join (by decide) sg10 sg34

lemma sg501 : RowSquare [3,3,1,1,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12 sg32

lemma sg502 : RowSquare [3,3,1,1,1] [5,2,2] := by
  exact rowSquare_join (by decide) sg1 sg114

lemma sg503 : RowSquare [3,3,1,1,1] [5,4] := by
  exact rowSquare_join (by decide) sg10 sg36

lemma sg504 : RowSquare [3,3,1,1,1] [6,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg21

lemma sg505 : RowSquare [3,3,1,1,1] [6,2,1] := by
  exact rowSquare_join (by decide) sg1 sg117

lemma sg506 : RowSquare [3,3,1,1,1] [6,3] := by
  exact rowSquare_join (by decide) sg1 sg118

lemma sg507 : RowSquare [3,3,1,1,1] [7,2] := by
  exact rowSquare_join (by decide) sg14 sg21

lemma sg508 : RowSquare [3,3,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg1 sg121

lemma sg510 : RowSquare [3,3,2,1] [2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg306

lemma sg512 : RowSquare [3,3,2,1] [3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg307

lemma sg514 : RowSquare [3,3,2,1] [3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg62

lemma sg515 : RowSquare [3,3,2,1] [4,4,1] := by
  exact rowSquare_join (by decide) sg10 sg27

lemma sg517 : RowSquare [4,1,1,1,1,1] [3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg178

lemma sg518 : RowSquare [4,1,1,1,1,1] [3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg371

lemma sg519 : RowSquare [4,1,1,1,1,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg372

lemma sg520 : RowSquare [4,1,1,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg373

lemma sg521 : RowSquare [4,1,1,1,1,1] [4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg179

lemma sg522 : RowSquare [4,1,1,1,1,1] [4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg180

lemma sg523 : RowSquare [4,1,1,1,1,1] [4,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg181

lemma sg524 : RowSquare [4,1,1,1,1,1] [4,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg377

lemma sg525 : RowSquare [4,1,1,1,1,1] [4,3,2] := by
  exact rowSquare_join (by decide) sg0 sg378

lemma sg526 : RowSquare [4,1,1,1,1,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg260

lemma sg527 : RowSquare [4,1,1,1,1,1] [5,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg261

lemma sg528 : RowSquare [4,1,1,1,1,1] [5,2,2] := by
  exact rowSquare_join (by decide) sg0 sg262

lemma sg529 : RowSquare [4,1,1,1,1,1] [5,3,1] := by
  exact rowSquare_join (by decide) sg2 sg185

lemma sg530 : RowSquare [4,1,1,1,1,1] [5,4] := by
  exact rowSquare_join (by decide) sg0 sg383

lemma sg531 : RowSquare [4,1,1,1,1,1] [6,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg263

lemma sg532 : RowSquare [4,1,1,1,1,1] [6,2,1] := by
  exact rowSquare_join (by decide) sg0 sg264

lemma sg533 : RowSquare [4,1,1,1,1,1] [6,3] := by
  exact rowSquare_join (by decide) sg0 sg265

lemma sg534 : RowSquare [4,2,1,1,1] [2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg330

lemma sg538 : RowSquare [4,2,1,1,1] [3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg178

lemma sg539 : RowSquare [4,2,1,1,1] [3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg332

lemma sg540 : RowSquare [4,2,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg271

lemma sg542 : RowSquare [4,2,1,1,1] [3,3,2,1] := by
  exact rowSquare_join (by decide) sg4 sg67

lemma sg543 : RowSquare [4,2,1,1,1] [3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg68

lemma sg544 : RowSquare [4,2,1,1,1] [4,4,1] := by
  exact rowSquare_join (by decide) sg4 sg71

lemma sg545 : RowSquare [4,2,1,1,1] [6,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg116

lemma sg546 : RowSquare [4,2,1,1,1] [6,2,1] := by
  exact rowSquare_join (by decide) sg4 sg53

lemma sg547 : RowSquare [4,2,1,1,1] [6,3] := by
  exact rowSquare_join (by decide) sg5 sg52

lemma sg554 : RowSquare [4,2,2,1] [3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg55

lemma sg555 : RowSquare [4,2,2,1] [4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg288

lemma sg556 : RowSquare [4,2,2,1] [4,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg123

lemma sg557 : RowSquare [4,2,2,1] [4,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg291

lemma sg558 : RowSquare [4,2,2,1] [4,3,2] := by
  exact rowSquare_join (by decide) sg0 sg292

lemma sg560 : RowSquare [4,2,2,1] [5,4] := by
  exact rowSquare_join (by decide) sg10 sg23

lemma sg566 : RowSquare [4,3,1,1] [3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg295

lemma sg567 : RowSquare [4,3,1,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg296

lemma sg568 : RowSquare [4,3,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg297

lemma sg571 : RowSquare [4,3,1,1] [3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg55

lemma sg572 : RowSquare [4,3,1,1] [4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg142

lemma sg573 : RowSquare [4,3,1,1] [4,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg23

lemma sg574 : RowSquare [4,3,1,1] [4,3,2] := by
  exact rowSquare_join (by decide) sg4 sg57

lemma sg576 : RowSquare [4,3,2] [2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg306

lemma sg585 : RowSquare [4,4,1] [4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg165

lemma sg587 : RowSquare [5,1,1,1,1] [2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg53

lemma sg588 : RowSquare [5,1,1,1,1] [2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg52

lemma sg589 : RowSquare [5,1,1,1,1] [2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg137

lemma sg590 : RowSquare [5,1,1,1,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg324

lemma sg591 : RowSquare [5,1,1,1,1] [3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg312

lemma sg592 : RowSquare [5,1,1,1,1] [3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg313

lemma sg593 : RowSquare [5,1,1,1,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg314

lemma sg594 : RowSquare [5,1,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg315

lemma sg595 : RowSquare [5,1,1,1,1] [3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg134

lemma sg596 : RowSquare [5,1,1,1,1] [3,3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg320

lemma sg597 : RowSquare [5,1,1,1,1] [4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg316

lemma sg598 : RowSquare [5,1,1,1,1] [4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg317

lemma sg599 : RowSquare [5,1,1,1,1] [4,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg318

lemma sg600 : RowSquare [5,1,1,1,1] [4,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg319

lemma sg601 : RowSquare [5,1,1,1,1] [4,3,2] := by
  exact rowSquare_join (by decide) sg0 sg320

lemma sg602 : RowSquare [5,1,1,1,1] [4,4,1] := by
  exact rowSquare_join (by decide) sg0 sg315

lemma sg603 : RowSquare [5,1,1,1,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg132

lemma sg604 : RowSquare [5,1,1,1,1] [5,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg133

lemma sg605 : RowSquare [5,1,1,1,1] [5,2,2] := by
  exact rowSquare_join (by decide) sg2 sg134

lemma sg606 : RowSquare [5,1,1,1,1] [5,3,1] := by
  exact rowSquare_join (by decide) sg0 sg323

lemma sg607 : RowSquare [5,1,1,1,1] [5,4] := by
  exact rowSquare_join (by decide) sg0 sg324

lemma sg608 : RowSquare [5,1,1,1,1] [6,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg135

lemma sg609 : RowSquare [5,1,1,1,1] [6,2,1] := by
  exact rowSquare_join (by decide) sg2 sg136

lemma sg610 : RowSquare [5,1,1,1,1] [6,3] := by
  exact rowSquare_join (by decide) sg2 sg137

lemma sg611 : RowSquare [5,1,1,1,1] [7,1,1] := by
  exact rowSquare_join (by decide) sg7 sg51

lemma sg612 : RowSquare [5,1,1,1,1] [7,2] := by
  exact rowSquare_join (by decide) sg7 sg52

lemma sg613 : RowSquare [5,2,1,1] [2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg330

lemma sg617 : RowSquare [5,2,1,1] [3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg178

lemma sg618 : RowSquare [5,2,1,1] [3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg332

lemma sg619 : RowSquare [5,2,1,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg66

lemma sg620 : RowSquare [5,2,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg334

lemma sg622 : RowSquare [5,2,1,1] [3,3,2,1] := by
  exact rowSquare_join (by decide) sg4 sg67

lemma sg623 : RowSquare [5,2,1,1] [3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg68

lemma sg624 : RowSquare [5,2,1,1] [4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg142

lemma sg625 : RowSquare [5,2,1,1] [4,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg69

lemma sg626 : RowSquare [5,2,1,1] [4,3,1,1] := by
  exact rowSquare_join (by decide) sg5 sg67

lemma sg627 : RowSquare [5,2,1,1] [4,3,2] := by
  exact rowSquare_join (by decide) sg4 sg70

lemma sg628 : RowSquare [5,2,1,1] [4,4,1] := by
  exact rowSquare_join (by decide) sg4 sg71

lemma sg629 : RowSquare [5,2,1,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg66

lemma sg630 : RowSquare [5,2,1,1] [5,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg69

lemma sg631 : RowSquare [5,2,1,1] [5,2,2] := by
  exact rowSquare_join (by decide) sg16 sg22

lemma sg632 : RowSquare [5,2,1,1] [5,4] := by
  exact rowSquare_join (by decide) sg17 sg23

lemma sg633 : RowSquare [5,2,1,1] [6,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg56

lemma sg634 : RowSquare [5,2,1,1] [6,2,1] := by
  exact rowSquare_join (by decide) sg16 sg24

lemma sg635 : RowSquare [5,2,1,1] [6,3] := by
  exact rowSquare_join (by decide) sg17 sg24

lemma sg638 : RowSquare [5,2,2] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg350

lemma sg639 : RowSquare [5,2,2] [3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg32

lemma sg642 : RowSquare [5,2,2] [5,4] := by
  exact rowSquare_join (by decide) sg10 sg36

lemma sg643 : RowSquare [5,3,1] [2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg74

lemma sg644 : RowSquare [5,3,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg32

lemma sg645 : RowSquare [5,3,1] [3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg74

lemma sg646 : RowSquare [5,3,1] [3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg32

lemma sg647 : RowSquare [5,3,1] [3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg77

lemma sg648 : RowSquare [5,3,1] [4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg74

lemma sg649 : RowSquare [5,3,1] [4,3,2] := by
  exact rowSquare_join (by decide) sg16 sg27

lemma sg650 : RowSquare [5,3,1] [4,4,1] := by
  exact rowSquare_join (by decide) sg17 sg27

lemma sg651 : RowSquare [5,3,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg32

lemma sg652 : RowSquare [5,3,1] [5,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg37

lemma sg653 : RowSquare [5,3,1] [5,2,2] := by
  exact rowSquare_join (by decide) sg16 sg28

lemma sg654 : RowSquare [5,3,1] [5,3,1] := by
  exact rowSquare_join (by decide) sg16 sg29

lemma sg655 : RowSquare [5,3,1] [5,4] := by
  exact rowSquare_join (by decide) sg17 sg29

lemma sg673 : RowSquare [6,1,1,1] [3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg178

lemma sg674 : RowSquare [6,1,1,1] [3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg371

lemma sg675 : RowSquare [6,1,1,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg372

lemma sg676 : RowSquare [6,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg373

lemma sg677 : RowSquare [6,1,1,1] [4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg179

lemma sg678 : RowSquare [6,1,1,1] [4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg180

lemma sg679 : RowSquare [6,1,1,1] [4,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg181

lemma sg680 : RowSquare [6,1,1,1] [4,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg377

lemma sg681 : RowSquare [6,1,1,1] [4,3,2] := by
  exact rowSquare_join (by decide) sg0 sg378

lemma sg682 : RowSquare [6,1,1,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg66

lemma sg683 : RowSquare [6,1,1,1] [5,2,1,1] := by
  exact rowSquare_join (by decide) sg7 sg67

lemma sg684 : RowSquare [6,1,1,1] [5,2,2] := by
  exact rowSquare_join (by decide) sg7 sg68

lemma sg685 : RowSquare [6,1,1,1] [5,3,1] := by
  exact rowSquare_join (by decide) sg2 sg185

lemma sg686 : RowSquare [6,1,1,1] [5,4] := by
  exact rowSquare_join (by decide) sg0 sg383

lemma sg687 : RowSquare [6,1,1,1] [6,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg69

lemma sg688 : RowSquare [6,1,1,1] [6,2,1] := by
  exact rowSquare_join (by decide) sg7 sg70

lemma sg689 : RowSquare [6,1,1,1] [6,3] := by
  exact rowSquare_join (by decide) sg7 sg71

lemma sg690 : RowSquare [6,1,1,1] [7,1,1] := by
  exact rowSquare_join (by decide) sg20 sg22

lemma sg691 : RowSquare [6,1,1,1] [7,2] := by
  exact rowSquare_join (by decide) sg20 sg23

lemma sg692 : RowSquare [6,2,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg16 sg32

lemma sg693 : RowSquare [6,2,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg390

lemma sg694 : RowSquare [6,2,1] [3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg32

lemma sg695 : RowSquare [6,2,1] [3,3,2,1] := by
  exact rowSquare_join (by decide) sg4 sg88

end UniversalTensorSquare
end
end

end OAI
