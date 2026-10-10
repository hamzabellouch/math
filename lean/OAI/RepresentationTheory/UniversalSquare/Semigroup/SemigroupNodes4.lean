import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes3

namespace OAI

/-! Semigroup Nodes 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2086 : RowSquare [4,4,1,1,1,1,1] [4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg66 sg180

lemma sg2087 : RowSquare [4,4,1,1,1,1,1] [5,3,3,2] := by
  exact rowSquare_join (by decide) sg69 sg181

lemma sg2088 : RowSquare [4,4,1,1,1,1,1] [5,4,4] := by
  exact rowSquare_join (by decide) sg68 sg184

lemma sg2089 : RowSquare [4,4,1,1,1,1,1] [5,5,3] := by
  exact rowSquare_join (by decide) sg68 sg185

lemma sg2090 : RowSquare [4,4,1,1,1,1,1] [6,4,3] := by
  exact rowSquare_join (by decide) sg1 sg1157

lemma sg2091 : RowSquare [4,4,1,1,1,1,1] [6,5,2] := by
  exact rowSquare_join (by decide) sg68 sg188

lemma sg2092 : RowSquare [4,4,1,1,1,1,1] [6,6,1] := by
  exact rowSquare_join (by decide) sg71 sg185

lemma sg2093 : RowSquare [4,4,1,1,1,1,1] [7,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg435

lemma sg2094 : RowSquare [4,4,1,1,1,1,1] [7,3,3] := by
  exact rowSquare_join (by decide) sg1 sg1162

lemma sg2095 : RowSquare [4,4,1,1,1,1,1] [7,4,2] := by
  exact rowSquare_join (by decide) sg14 sg432

lemma sg2096 : RowSquare [4,4,1,1,1,1,1] [7,5,1] := by
  exact rowSquare_join (by decide) sg14 sg433

lemma sg2097 : RowSquare [4,4,1,1,1,1,1] [7,6] := by
  exact rowSquare_join (by decide) sg14 sg434

lemma sg2098 : RowSquare [4,4,1,1,1,1,1] [8,3,2] := by
  exact rowSquare_join (by decide) sg1 sg1167

lemma sg2099 : RowSquare [4,4,1,1,1,1,1] [8,5] := by
  exact rowSquare_join (by decide) sg14 sg437

lemma sg2100 : RowSquare [4,4,1,1,1,1,1] [9,2,2] := by
  exact rowSquare_join (by decide) sg83 sg109

lemma sg2101 : RowSquare [4,4,1,1,1,1,1] [9,4] := by
  exact rowSquare_join (by decide) sg14 sg438

lemma sg2102 : RowSquare [4,4,1,1,1,1,1] [10,3] := by
  exact rowSquare_join (by decide) sg14 sg439

lemma sg2103 : RowSquare [4,4,1,1,1,1,1] [11,2] := by
  exact rowSquare_join (by decide) sg85 sg109

lemma sg2104 : RowSquare [4,4,1,1,1,1,1] [12,1] := by
  exact rowSquare_join (by decide) sg15 sg439

lemma sg2106 : RowSquare [4,4,2,2,1] [3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg1654

lemma sg2108 : RowSquare [4,4,3,2] [2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg60 sg131

lemma sg2109 : RowSquare [4,4,3,2] [2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg59 sg131

lemma sg2110 : RowSquare [4,4,3,2] [2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg59 sg130

lemma sg2111 : RowSquare [4,4,3,2] [2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg29 sg257

lemma sg2112 : RowSquare [4,4,3,2] [3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg58 sg131

lemma sg2113 : RowSquare [4,4,3,2] [3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg55 sg131

lemma sg2114 : RowSquare [5,1,1,1,1,1,1,1,1] [8,5] := by
  exact rowSquare_join (by decide) sg7 sg1023

lemma sg2115 : RowSquare [5,2,1,1,1,1,1,1] [3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg999

lemma sg2116 : RowSquare [5,2,1,1,1,1,1,1] [4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg1000

lemma sg2117 : RowSquare [5,2,1,1,1,1,1,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg588

lemma sg2118 : RowSquare [5,2,1,1,1,1,1,1] [4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg589

lemma sg2119 : RowSquare [5,2,2,1,1,1,1] [2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg910

lemma sg2120 : RowSquare [5,2,2,1,1,1,1] [2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg586

lemma sg2121 : RowSquare [5,3,1,1,1,1,1] [3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg9 sg586

lemma sg2122 : RowSquare [5,3,1,1,1,1,1] [3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg586

lemma sg2123 : RowSquare [5,3,1,1,1,1,1] [3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg313

lemma sg2124 : RowSquare [5,3,1,1,1,1,1] [3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg32 sg314

lemma sg2125 : RowSquare [5,3,1,1,1,1,1] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg315

lemma sg2126 : RowSquare [5,3,1,1,1,1,1] [4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg11 sg586

lemma sg2127 : RowSquare [5,3,1,1,1,1,1] [4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg9 sg587

lemma sg2128 : RowSquare [5,3,1,1,1,1,1] [4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg587

lemma sg2129 : RowSquare [5,3,1,1,1,1,1] [4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg9 sg589

lemma sg2130 : RowSquare [5,3,1,1,1,1,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg588

lemma sg2131 : RowSquare [5,3,1,1,1,1,1] [4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg319

lemma sg2132 : RowSquare [5,3,1,1,1,1,1] [5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12 sg586

lemma sg2133 : RowSquare [5,3,1,1,1,1,1] [5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg324

lemma sg2134 : RowSquare [5,3,2,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1682

lemma sg2135 : RowSquare [5,3,2,1,1,1] [3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg1688

lemma sg2136 : RowSquare [5,3,2,1,1,1] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg271

lemma sg2138 : RowSquare [5,3,3,1,1] [2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg64 sg141

lemma sg2139 : RowSquare [5,3,3,1,1] [2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg64 sg139

lemma sg2140 : RowSquare [5,3,3,1,1] [2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg64 sg137

lemma sg2141 : RowSquare [5,3,3,1,1] [2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg36 sg252

lemma sg2142 : RowSquare [5,3,3,1,1] [3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg51 sg163

lemma sg2143 : RowSquare [5,3,3,1,1] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg52 sg160

lemma sg2144 : RowSquare [5,3,3,1,1] [3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg34 sg252

lemma sg2145 : RowSquare [5,3,3,1,1] [3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg62 sg141

lemma sg2146 : RowSquare [5,3,3,1,1] [3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg62 sg140

lemma sg2147 : RowSquare [5,4,3,1] [3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg798

lemma sg2148 : RowSquare [5,4,3,1] [4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg798

lemma sg2149 : RowSquare [5,4,3,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg511

lemma sg2150 : RowSquare [5,4,3,1] [5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg798

lemma sg2151 : RowSquare [5,5,2,1] [5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg513

lemma sg2152 : RowSquare [5,5,2,1] [7,6] := by
  exact rowSquare_join (by decide) sg29 sg302

lemma sg2153 : RowSquare [5,5,3] [2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg516

lemma sg2154 : RowSquare [6,1,1,1,1,1,1,1] [5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg1340

lemma sg2155 : RowSquare [6,1,1,1,1,1,1,1] [7,5,1] := by
  exact rowSquare_join (by decide) sg2 sg1358

lemma sg2156 : RowSquare [6,2,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1754

lemma sg2157 : RowSquare [6,2,1,1,1,1,1] [3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1757

lemma sg2158 : RowSquare [6,2,1,1,1,1,1] [3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg889

lemma sg2159 : RowSquare [6,2,1,1,1,1,1] [3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg891

lemma sg2160 : RowSquare [6,2,1,1,1,1,1] [3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg892

lemma sg2161 : RowSquare [6,2,1,1,1,1,1] [4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg1331

lemma sg2162 : RowSquare [6,2,1,1,1,1,1] [4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg1332

lemma sg2163 : RowSquare [6,2,1,1,1,1,1] [4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg891

lemma sg2164 : RowSquare [6,2,1,1,1,1,1] [4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg892

lemma sg2165 : RowSquare [6,2,1,1,1,1,1] [4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg897

lemma sg2166 : RowSquare [6,2,2,1,1,1] [3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg808

lemma sg2167 : RowSquare [6,3,2,1,1] [3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg1688

lemma sg2168 : RowSquare [6,3,3,1] [3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg285

lemma sg2169 : RowSquare [6,3,3,1] [4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1233

lemma sg2170 : RowSquare [6,3,3,1] [4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg66 sg154

lemma sg2171 : RowSquare [6,3,3,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg549

lemma sg2172 : RowSquare [6,3,3,1] [5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg798

lemma sg2173 : RowSquare [6,4,2,1] [2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg849

lemma sg2174 : RowSquare [6,4,2,1] [3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg849

lemma sg2175 : RowSquare [6,4,2,1] [3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg850

lemma sg2176 : RowSquare [6,4,2,1] [3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg330

lemma sg2177 : RowSquare [6,4,2,1] [3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg142

lemma sg2178 : RowSquare [6,4,2,1] [3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg27 sg330

lemma sg2179 : RowSquare [6,4,2,1] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg549

lemma sg2180 : RowSquare [6,4,2,1] [3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg143

lemma sg2181 : RowSquare [6,4,2,1] [3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg852

lemma sg2182 : RowSquare [6,4,2,1] [3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg144

lemma sg2183 : RowSquare [6,4,2,1] [3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg32 sg296

lemma sg2184 : RowSquare [6,4,2,1] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg297

lemma sg2185 : RowSquare [6,4,2,1] [4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg849

lemma sg2186 : RowSquare [6,4,2,1] [4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg850

lemma sg2187 : RowSquare [6,4,2,1] [4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg331

lemma sg2188 : RowSquare [6,4,2,1] [4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg145

lemma sg2189 : RowSquare [6,4,2,1] [4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg146

lemma sg2190 : RowSquare [6,4,2,1] [4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg75 sg143

lemma sg2191 : RowSquare [6,4,2,1] [4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg147

lemma sg2192 : RowSquare [6,4,2,1] [4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg75 sg144

lemma sg2193 : RowSquare [6,4,2,1] [4,3,3,3] := by
  exact rowSquare_join (by decide) sg39 sg287

lemma sg2194 : RowSquare [6,4,2,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg511

lemma sg2195 : RowSquare [6,4,2,1] [4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg148

lemma sg2196 : RowSquare [6,4,2,1] [4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg76 sg143

lemma sg2197 : RowSquare [6,4,2,1] [4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg77 sg143

lemma sg2198 : RowSquare [6,4,2,1] [4,4,3,2] := by
  exact rowSquare_join (by decide) sg76 sg144

lemma sg2199 : RowSquare [6,4,2,1] [4,4,4,1] := by
  exact rowSquare_join (by decide) sg97 sg123

lemma sg2200 : RowSquare [6,4,2,1] [5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg850

lemma sg2201 : RowSquare [6,4,2,1] [5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg149

lemma sg2202 : RowSquare [6,4,2,1] [5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg75 sg145

lemma sg2203 : RowSquare [6,4,2,1] [5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg75 sg147

lemma sg2204 : RowSquare [6,4,2,1] [5,3,3,2] := by
  exact rowSquare_join (by decide) sg98 sg123

lemma sg2205 : RowSquare [6,4,2,1] [5,4,4] := by
  exact rowSquare_join (by decide) sg97 sg124

lemma sg2206 : RowSquare [6,4,2,1] [5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg143

lemma sg2207 : RowSquare [6,4,2,1] [5,5,2,1] := by
  exact rowSquare_join (by decide) sg76 sg148

lemma sg2208 : RowSquare [6,4,2,1] [5,5,3] := by
  exact rowSquare_join (by decide) sg97 sg125

lemma sg2209 : RowSquare [6,4,2,1] [6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg30 sg331

lemma sg2210 : RowSquare [6,4,2,1] [6,5,1,1] := by
  exact rowSquare_join (by decide) sg76 sg151

lemma sg2211 : RowSquare [6,4,2,1] [6,6,1] := by
  exact rowSquare_join (by decide) sg80 sg148

lemma sg2212 : RowSquare [6,4,3] [2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg306

lemma sg2213 : RowSquare [6,4,3] [3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg516

lemma sg2214 : RowSquare [6,4,3] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg307

lemma sg2215 : RowSquare [6,4,3] [3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg154

lemma sg2216 : RowSquare [6,4,3] [3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg516

lemma sg2217 : RowSquare [6,4,3] [3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg874

lemma sg2218 : RowSquare [6,4,3] [3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg156

lemma sg2219 : RowSquare [6,4,3] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg310

lemma sg2220 : RowSquare [6,4,3] [4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg307

lemma sg2221 : RowSquare [6,4,3] [5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg516

lemma sg2222 : RowSquare [6,5,1,1] [3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg561

lemma sg2223 : RowSquare [6,5,1,1] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg562

lemma sg2224 : RowSquare [6,5,1,1] [3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg877

lemma sg2225 : RowSquare [6,5,1,1] [3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg563

lemma sg2226 : RowSquare [6,5,1,1] [3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg879

lemma sg2227 : RowSquare [6,5,1,1] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg564

lemma sg2228 : RowSquare [6,5,1,1] [4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg880

lemma sg2229 : RowSquare [6,5,1,1] [4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg565

lemma sg2230 : RowSquare [6,5,1,1] [4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg561

lemma sg2231 : RowSquare [6,5,1,1] [4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg881

lemma sg2232 : RowSquare [6,5,1,1] [4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg295

lemma sg2233 : RowSquare [6,5,1,1] [4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg879

lemma sg2234 : RowSquare [6,5,1,1] [4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg142

lemma sg2235 : RowSquare [6,5,1,1] [4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg39 sg296

lemma sg2236 : RowSquare [6,5,1,1] [4,3,3,3] := by
  exact rowSquare_join (by decide) sg39 sg297

lemma sg2237 : RowSquare [6,5,1,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg562

lemma sg2238 : RowSquare [6,5,1,1] [4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg295

lemma sg2239 : RowSquare [6,5,1,1] [4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg569

lemma sg2240 : RowSquare [6,5,1,1] [4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg83 sg143

lemma sg2241 : RowSquare [6,5,1,1] [4,4,3,2] := by
  exact rowSquare_join (by decide) sg40 sg297

lemma sg2242 : RowSquare [6,5,1,1] [4,4,4,1] := by
  exact rowSquare_join (by decide) sg83 sg144

lemma sg2243 : RowSquare [6,5,1,1] [5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg880

lemma sg2244 : RowSquare [6,5,1,1] [5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg84 sg142

lemma sg2245 : RowSquare [6,5,1,1] [5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6 sg879

lemma sg2246 : RowSquare [6,5,1,1] [5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg569

lemma sg2247 : RowSquare [6,5,2] [3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg165

lemma sg2248 : RowSquare [6,5,2] [3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg306

lemma sg2249 : RowSquare [6,6,1] [4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg579

lemma sg2250 : RowSquare [6,6,1] [5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg583

lemma sg2252 : RowSquare [7,1,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg237

lemma sg2253 : RowSquare [7,1,1,1,1,1,1] [2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg236

lemma sg2254 : RowSquare [7,1,1,1,1,1,1] [2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg451

lemma sg2255 : RowSquare [7,1,1,1,1,1,1] [2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg806

lemma sg2256 : RowSquare [7,1,1,1,1,1,1] [2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1256

lemma sg2257 : RowSquare [7,1,1,1,1,1,1] [3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg450

lemma sg2258 : RowSquare [7,1,1,1,1,1,1] [3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg805

lemma sg2259 : RowSquare [7,1,1,1,1,1,1] [3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1255

lemma sg2260 : RowSquare [7,1,1,1,1,1,1] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1753

lemma sg2261 : RowSquare [7,1,1,1,1,1,1] [3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg449

lemma sg2262 : RowSquare [7,1,1,1,1,1,1] [3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg804

lemma sg2263 : RowSquare [7,1,1,1,1,1,1] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1254

lemma sg2264 : RowSquare [7,1,1,1,1,1,1] [4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg803

lemma sg2265 : RowSquare [7,1,1,1,1,1,1] [4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1252

lemma sg2266 : RowSquare [7,1,1,1,1,1,1] [4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1752

lemma sg2267 : RowSquare [7,1,1,1,1,1,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg801

lemma sg2268 : RowSquare [7,1,1,1,1,1,1] [4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1251

lemma sg2269 : RowSquare [7,1,1,1,1,1,1] [5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1244

lemma sg2270 : RowSquare [7,2,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1754

lemma sg2271 : RowSquare [7,2,1,1,1,1] [3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1755

lemma sg2272 : RowSquare [7,2,1,1,1,1] [3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1757

lemma sg2273 : RowSquare [7,2,1,1,1,1] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1758

lemma sg2274 : RowSquare [7,2,1,1,1,1] [3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg889

lemma sg2275 : RowSquare [7,2,1,1,1,1] [3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg890

lemma sg2276 : RowSquare [7,2,1,1,1,1] [3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg891

lemma sg2277 : RowSquare [7,2,1,1,1,1] [3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg892

lemma sg2278 : RowSquare [7,2,1,1,1,1] [4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg1332

lemma sg2279 : RowSquare [7,2,2,1,1] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg312

lemma sg2280 : RowSquare [7,2,2,1,1] [3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg586

lemma sg2281 : RowSquare [7,2,2,1,1] [3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg313

lemma sg2282 : RowSquare [7,2,2,1,1] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg315

lemma sg2283 : RowSquare [7,2,2,1,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg588

lemma sg2284 : RowSquare [7,2,2,2] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg66 sg178

lemma sg2285 : RowSquare [7,2,2,2] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg67 sg178

lemma sg2286 : RowSquare [7,2,2,2] [4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg66 sg179

lemma sg2287 : RowSquare [7,3,1,1,1] [2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg910

lemma sg2288 : RowSquare [7,3,1,1,1] [2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg586

lemma sg2289 : RowSquare [7,3,1,1,1] [3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg911

lemma sg2290 : RowSquare [7,3,1,1,1] [3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg587

lemma sg2291 : RowSquare [7,3,1,1,1] [3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg586

lemma sg2292 : RowSquare [7,3,1,1,1] [3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg912

lemma sg2293 : RowSquare [7,3,1,1,1] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg588

lemma sg2294 : RowSquare [7,3,1,1,1] [3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg913

lemma sg2295 : RowSquare [7,3,1,1,1] [3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg589

lemma sg2296 : RowSquare [7,3,1,1,1] [3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg915

lemma sg2297 : RowSquare [7,3,1,1,1] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg590

lemma sg2298 : RowSquare [7,3,1,1,1] [4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg911

lemma sg2299 : RowSquare [7,3,1,1,1] [4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg534

lemma sg2300 : RowSquare [7,3,1,1,1] [4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg312

lemma sg2301 : RowSquare [7,3,1,1,1] [4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg534

lemma sg2302 : RowSquare [7,3,1,1,1] [4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg915

lemma sg2303 : RowSquare [7,3,1,1,1] [4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg536

lemma sg2304 : RowSquare [7,3,1,1,1] [4,3,3,3] := by
  exact rowSquare_join (by decide) sg39 sg315

lemma sg2305 : RowSquare [7,3,1,1,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg535

lemma sg2306 : RowSquare [7,3,1,1,1] [4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg313

lemma sg2307 : RowSquare [7,3,1,1,1] [4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg595

lemma sg2308 : RowSquare [7,3,1,1,1] [4,4,4,1] := by
  exact rowSquare_join (by decide) sg4 sg923

lemma sg2309 : RowSquare [7,3,1,1,1] [5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg541

lemma sg2310 : RowSquare [7,3,2,1] [2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg330

lemma sg2311 : RowSquare [7,3,2,1] [2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg178

lemma sg2312 : RowSquare [7,3,2,1] [3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg330

lemma sg2313 : RowSquare [7,3,2,1] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg75 sg178

lemma sg2314 : RowSquare [7,3,2,1] [3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg179

lemma sg2315 : RowSquare [7,3,2,1] [3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg34 sg330

lemma sg2316 : RowSquare [7,3,2,1] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg76 sg178

lemma sg2317 : RowSquare [7,3,2,1] [3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg180

lemma sg2318 : RowSquare [7,3,2,1] [3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg181

lemma sg2319 : RowSquare [7,3,2,1] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg334

lemma sg2320 : RowSquare [7,3,2,1] [4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg35 sg330

lemma sg2321 : RowSquare [7,3,2,1] [4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg36 sg330

lemma sg2322 : RowSquare [7,3,2,1] [4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg79 sg178

lemma sg2323 : RowSquare [7,3,2,1] [4,3,3,3] := by
  exact rowSquare_join (by decide) sg33 sg334

lemma sg2324 : RowSquare [7,3,2,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg178

lemma sg2325 : RowSquare [7,3,2,1] [4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg88 sg143

lemma sg2326 : RowSquare [7,3,2,1] [5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg850

lemma sg2327 : RowSquare [7,3,2,1] [5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg81 sg178

lemma sg2328 : RowSquare [7,3,2,1] [5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg92 sg143

lemma sg2329 : RowSquare [7,3,3] [3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg348

lemma sg2330 : RowSquare [7,3,3] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg350

lemma sg2331 : RowSquare [7,3,3] [4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg87 sg155

lemma sg2332 : RowSquare [7,3,3] [4,3,3,3] := by
  exact rowSquare_join (by decide) sg33 sg350

lemma sg2333 : RowSquare [7,3,3] [4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg34 sg348

lemma sg2334 : RowSquare [7,3,3] [4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg88 sg155

lemma sg2335 : RowSquare [7,3,3] [5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg516

lemma sg2336 : RowSquare [7,3,3] [5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg87 sg158

lemma sg2337 : RowSquare [7,4,1,1] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg616

lemma sg2338 : RowSquare [7,4,1,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg562

lemma sg2339 : RowSquare [7,4,2] [3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg193

lemma sg2340 : RowSquare [7,4,2] [3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg194

lemma sg2341 : RowSquare [7,4,2] [3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg975

lemma sg2342 : RowSquare [7,4,2] [3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg195

lemma sg2343 : RowSquare [7,4,2] [3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg32 sg357

lemma sg2344 : RowSquare [7,4,2] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg358

lemma sg2345 : RowSquare [7,4,2] [4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg306

lemma sg2346 : RowSquare [7,4,2] [4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg306

lemma sg2347 : RowSquare [7,4,2] [4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg577

lemma sg2348 : RowSquare [7,4,2] [4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg87 sg166

lemma sg2349 : RowSquare [7,4,2] [4,3,3,3] := by
  exact rowSquare_join (by decide) sg39 sg350

lemma sg2350 : RowSquare [7,4,2] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg577

lemma sg2351 : RowSquare [7,4,2] [4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg88 sg166

lemma sg2352 : RowSquare [7,4,2] [5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg47 sg306

lemma sg2353 : RowSquare [7,4,2] [5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg307

lemma sg2354 : RowSquare [7,4,2] [5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg87 sg168

lemma sg2355 : RowSquare [7,4,2] [5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg307

lemma sg2356 : RowSquare [7,4,2] [6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg48 sg306

lemma sg2357 : RowSquare [7,4,2] [6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg47 sg307

lemma sg2358 : RowSquare [7,4,2] [7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg48 sg307

lemma sg2359 : RowSquare [7,5,1] [3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg207

lemma sg2360 : RowSquare [7,5,1] [3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg982

lemma sg2361 : RowSquare [7,5,1] [4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg210

lemma sg2362 : RowSquare [7,5,1] [4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg97 sg166

lemma sg2363 : RowSquare [7,5,1] [5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg367

lemma sg2365 : RowSquare [8,1,1,1,1,1] [3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1327

lemma sg2366 : RowSquare [8,1,1,1,1,1] [4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1330

lemma sg2367 : RowSquare [8,1,1,1,1,1] [4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1331

lemma sg2368 : RowSquare [8,1,1,1,1,1] [4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg1332

lemma sg2369 : RowSquare [8,2,1,1,1] [3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg586

lemma sg2370 : RowSquare [8,2,1,1,1] [3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg586

lemma sg2371 : RowSquare [8,2,1,1,1] [3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg998

lemma sg2372 : RowSquare [8,2,1,1,1] [3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg999

lemma sg2373 : RowSquare [8,2,1,1,1] [3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1000

lemma sg2374 : RowSquare [8,2,1,1,1] [3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg1001

lemma sg2375 : RowSquare [8,2,1,1,1] [4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg586

lemma sg2376 : RowSquare [8,2,1,1,1] [4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg587

lemma sg2377 : RowSquare [8,2,1,1,1] [4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg587

lemma sg2378 : RowSquare [8,2,1,1,1] [4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg588

lemma sg2379 : RowSquare [8,2,1,1,1] [4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg1000

lemma sg2380 : RowSquare [8,2,1,1,1] [4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg1001

lemma sg2381 : RowSquare [8,2,1,1,1] [4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg16 sg590

lemma sg2382 : RowSquare [8,2,1,1,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg588

lemma sg2383 : RowSquare [8,2,1,1,1] [4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg589

lemma sg2384 : RowSquare [8,2,1,1,1] [4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg17 sg590

lemma sg2385 : RowSquare [8,2,1,1,1] [4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1007

lemma sg2386 : RowSquare [8,2,1,1,1] [4,4,3,2] := by
  exact rowSquare_join (by decide) sg4 sg1008

lemma sg2387 : RowSquare [8,2,1,1,1] [5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18 sg590

lemma sg2388 : RowSquare [8,2,1,1,1] [5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg595

lemma sg2389 : RowSquare [8,2,1,1,1] [5,5,2,1] := by
  exact rowSquare_join (by decide) sg17 sg596

lemma sg2390 : RowSquare [8,2,2,1] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg87 sg178

lemma sg2391 : RowSquare [8,2,2,1] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg88 sg178

lemma sg2392 : RowSquare [8,2,2,1] [3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg371

lemma sg2393 : RowSquare [8,2,2,1] [3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg178

lemma sg2394 : RowSquare [8,2,2,1] [3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg32 sg372

lemma sg2395 : RowSquare [8,2,2,1] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg373

lemma sg2396 : RowSquare [8,2,2,1] [4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg87 sg179

lemma sg2397 : RowSquare [8,2,2,1] [4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg179

lemma sg2398 : RowSquare [8,2,2,1] [4,3,3,3] := by
  exact rowSquare_join (by decide) sg33 sg373

lemma sg2399 : RowSquare [8,2,2,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg92 sg178

lemma sg2400 : RowSquare [8,2,2,1] [4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg34 sg371

lemma sg2401 : RowSquare [8,2,2,1] [4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg88 sg180

lemma sg2402 : RowSquare [8,2,2,1] [4,4,4,1] := by
  exact rowSquare_join (by decide) sg89 sg181

lemma sg2403 : RowSquare [8,2,2,1] [5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg940

lemma sg2404 : RowSquare [8,2,2,1] [6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg548

lemma sg2405 : RowSquare [8,3,1,1] [3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg178

lemma sg2406 : RowSquare [8,3,1,1] [3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1032

lemma sg2407 : RowSquare [8,3,1,1] [3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg1033

lemma sg2408 : RowSquare [8,3,1,1] [4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg330

lemma sg2409 : RowSquare [8,3,1,1] [4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg98 sg178

lemma sg2410 : RowSquare [8,3,1,1] [4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg330

lemma sg2411 : RowSquare [8,3,1,1] [4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg99 sg178

lemma sg2412 : RowSquare [8,3,1,1] [4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg371

lemma sg2413 : RowSquare [8,3,1,1] [4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg1033

lemma sg2414 : RowSquare [8,3,1,1] [4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg179

lemma sg2415 : RowSquare [8,3,1,1] [4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg39 sg372

lemma sg2416 : RowSquare [8,3,1,1] [4,3,3,3] := by
  exact rowSquare_join (by decide) sg39 sg373

lemma sg2417 : RowSquare [8,3,1,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg614

lemma sg2418 : RowSquare [8,3,1,1] [4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg371

lemma sg2419 : RowSquare [8,3,1,1] [4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg17 sg616

lemma sg2420 : RowSquare [8,3,1,1] [4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg97 sg180

lemma sg2421 : RowSquare [8,3,1,1] [4,4,3,2] := by
  exact rowSquare_join (by decide) sg40 sg373

lemma sg2422 : RowSquare [8,3,1,1] [4,4,4,1] := by
  exact rowSquare_join (by decide) sg97 sg181

lemma sg2423 : RowSquare [8,3,1,1] [5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg47 sg330

lemma sg2424 : RowSquare [8,3,1,1] [5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg100 sg178

lemma sg2425 : RowSquare [8,3,1,1] [5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg98 sg179

lemma sg2426 : RowSquare [8,3,1,1] [5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg7 sg961

lemma sg2427 : RowSquare [8,3,1,1] [5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg101 sg178

lemma sg2428 : RowSquare [8,3,1,1] [5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg99 sg179

lemma sg2429 : RowSquare [8,3,1,1] [5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg332

lemma sg2430 : RowSquare [8,3,1,1] [5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg66 sg228

lemma sg2431 : RowSquare [8,3,1,1] [5,4,2,2] := by
  exact rowSquare_join (by decide) sg39 sg377

lemma sg2432 : RowSquare [8,3,2] [3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg32 sg389

lemma sg2433 : RowSquare [8,3,2] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg390

lemma sg2434 : RowSquare [8,3,2] [4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg218

lemma sg2435 : RowSquare [8,3,2] [4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg219

lemma sg2436 : RowSquare [8,3,2] [4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg87 sg194

lemma sg2437 : RowSquare [8,3,2] [4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg220

lemma sg2438 : RowSquare [8,3,2] [4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg87 sg195

lemma sg2439 : RowSquare [8,3,2] [4,3,3,3] := by
  exact rowSquare_join (by decide) sg33 sg390

lemma sg2440 : RowSquare [8,3,2] [4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg636

lemma sg2441 : RowSquare [8,3,2] [4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg88 sg194

lemma sg2442 : RowSquare [8,3,2] [4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg89 sg194

lemma sg2443 : RowSquare [8,3,2] [4,4,3,2] := by
  exact rowSquare_join (by decide) sg88 sg195

lemma sg2444 : RowSquare [8,3,2] [5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg975

lemma sg2445 : RowSquare [8,3,2] [5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg221

lemma sg2446 : RowSquare [8,3,2] [5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg87 sg196

lemma sg2447 : RowSquare [8,3,2] [5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg87 sg197

lemma sg2448 : RowSquare [8,3,2] [5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg223

lemma sg2449 : RowSquare [8,3,2] [5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg92 sg194

lemma sg2450 : RowSquare [8,3,2] [6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg577

lemma sg2451 : RowSquare [8,4,1] [4,3,3,3] := by
  exact rowSquare_join (by decide) sg39 sg390

lemma sg2452 : RowSquare [8,4,1] [4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg402

lemma sg2453 : RowSquare [8,4,1] [5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg7 sg982

lemma sg2454 : RowSquare [9,1,1,1,1] [5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg998

lemma sg2455 : RowSquare [9,1,1,1,1] [5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg999

lemma sg2456 : RowSquare [9,2,1,1] [5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg104 sg178

lemma sg2457 : RowSquare [9,2,1,1] [5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg7 sg1033

lemma sg2458 : RowSquare [9,2,1,1] [5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg178

lemma sg2459 : RowSquare [9,2,1,1] [5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg45 sg372

lemma sg2460 : RowSquare [9,2,1,1] [5,3,3,2] := by
  exact rowSquare_join (by decide) sg45 sg373

lemma sg2461 : RowSquare [9,2,2] [5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg87 sg218

lemma sg2462 : RowSquare [9,2,2] [5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg87 sg219

lemma sg2463 : RowSquare [9,2,2] [5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg87 sg220

lemma sg2464 : RowSquare [9,2,2] [5,4,2,2] := by
  exact rowSquare_join (by decide) sg88 sg219

lemma sg2465 : RowSquare [9,2,2] [5,4,3,1] := by
  exact rowSquare_join (by decide) sg88 sg220

lemma sg2466 : RowSquare [9,2,2] [6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg636

lemma sg2467 : RowSquare [9,2,2] [6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg87 sg221

lemma sg2468 : RowSquare [9,2,2] [6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg1063

lemma sg2469 : RowSquare [9,2,2] [6,3,2,1,1] := by
  exact rowSquare_join (by decide) sg87 sg222

lemma sg2470 : RowSquare [9,2,2] [6,3,2,2] := by
  exact rowSquare_join (by decide) sg88 sg221

lemma sg2471 : RowSquare [9,2,2] [6,3,3,1] := by
  exact rowSquare_join (by decide) sg90 sg220

lemma sg2472 : RowSquare [9,2,2] [6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg87 sg223

lemma sg2473 : RowSquare [9,2,2] [6,4,2,1] := by
  exact rowSquare_join (by decide) sg88 sg222

lemma sg2474 : RowSquare [9,2,2] [6,4,3] := by
  exact rowSquare_join (by decide) sg89 sg222

lemma sg2475 : RowSquare [9,2,2] [6,5,1,1] := by
  exact rowSquare_join (by decide) sg88 sg223

lemma sg2476 : RowSquare [9,2,2] [6,5,2] := by
  exact rowSquare_join (by decide) sg89 sg223

lemma sg2477 : RowSquare [9,2,2] [7,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg348

lemma sg2478 : RowSquare [9,3,1] [5,4,2,2] := by
  exact rowSquare_join (by decide) sg46 sg390

lemma sg2479 : RowSquare [9,3,1] [5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg424

lemma sg2480 : RowSquare [10,2,1] [7,2,2,1,1] := by
  exact rowSquare_join (by decide) sg87 sg231

lemma sg2481 : RowSquare [10,2,1] [7,2,2,2] := by
  exact rowSquare_join (by decide) sg49 sg390

lemma sg2482 : RowSquare [10,2,1] [7,3,1,1,1] := by
  exact rowSquare_join (by decide) sg87 sg232

lemma sg2483 : RowSquare [10,2,1] [7,3,2,1] := by
  exact rowSquare_join (by decide) sg88 sg231

lemma sg2484 : RowSquare [10,2,1] [7,3,3] := by
  exact rowSquare_join (by decide) sg89 sg231

lemma sg2485 : RowSquare [2,2,1,1,1,1,1,1,1,1,1,1] [10,2,2] := by
  exact rowSquare_join (by decide) sg227 sg234

lemma sg2486 : RowSquare [2,2,2,2,1,1,1,1,1,1] [7,5,1,1] := by
  exact rowSquare_join (by decide) sg98 sg424

lemma sg2487 : RowSquare [2,2,2,2,1,1,1,1,1,1] [7,6,1] := by
  exact rowSquare_join (by decide) sg228 sg230

lemma sg2490 : RowSquare [3,2,2,1,1,1,1,1,1,1] [7,7] := by
  exact rowSquare_join (by decide) sg92 sg424

lemma sg2491 : RowSquare [3,2,2,2,1,1,1,1,1] [4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg97 sg389

lemma sg2492 : RowSquare [3,2,2,2,1,1,1,1,1] [4,4,4,2] := by
  exact rowSquare_join (by decide) sg97 sg390

end UniversalTensorSquare
end
end

end OAI
