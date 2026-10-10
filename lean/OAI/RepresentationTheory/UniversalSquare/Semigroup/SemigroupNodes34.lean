import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes13
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes14
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes9

namespace OAI

/-! Semigroup Nodes 34. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14140 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,2] := by
  exact rowSquare_join (by decide) sg2373 sg2783

lemma sg14141 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,3,1] := by
  exact rowSquare_join (by decide) sg2373 sg2784

lemma sg14142 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4] := by
  exact rowSquare_join (by decide) sg2374 sg2784

lemma sg14143 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,1] := by
  exact rowSquare_join (by decide) sg2297 sg2961

lemma sg14144 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3] := by
  exact rowSquare_join (by decide) sg2297 sg2962

lemma sg14145 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,4,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2288 sg2979

lemma sg14146 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2289 sg2963

lemma sg14147 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2288 sg2980

lemma sg14148 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2981

lemma sg14149 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2290 sg2964

lemma sg14150 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2369 sg2785

lemma sg14151 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2288 sg2982

lemma sg14152 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2369 sg2786

lemma sg14153 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2983

lemma sg14154 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2290 sg2966

lemma sg14155 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2984

lemma sg14156 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2290 sg2967

lemma sg14157 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2985

lemma sg14158 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2369 sg2787

lemma sg14159 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1876 sg3651

lemma sg14160 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2986

lemma sg14161 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2290 sg2968

lemma sg14162 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2369 sg2788

lemma sg14163 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2987

lemma sg14164 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2290 sg2969

lemma sg14165 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg2300 sg2960

lemma sg14166 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2988

lemma sg14167 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg2300 sg2961

lemma sg14168 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg2300 sg2962

lemma sg14169 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2370 sg2785

lemma sg14170 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2989

lemma sg14171 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2369 sg2791

lemma sg14172 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2990

lemma sg14173 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2369 sg2793

lemma sg14174 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2991

lemma sg14175 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg2293 sg2967

lemma sg14176 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2369 sg2794

lemma sg14177 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2992

lemma sg14178 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2293 sg2968

lemma sg14179 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2993

lemma sg14180 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg2293 sg2969

lemma sg14181 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2293 sg2970

lemma sg14182 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg2293 sg2971

lemma sg14183 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,2,2] := by
  exact rowSquare_join (by decide) sg2379 sg2783

lemma sg14184 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,3,1] := by
  exact rowSquare_join (by decide) sg2379 sg2784

lemma sg14185 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,4] := by
  exact rowSquare_join (by decide) sg2380 sg2784

lemma sg14186 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2370 sg2791

lemma sg14187 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2371 sg2790

lemma sg14188 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2994

lemma sg14189 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2370 sg2793

lemma sg14190 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2370 sg2794

lemma sg14191 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2995

lemma sg14192 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2371 sg2793

lemma sg14193 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2996

lemma sg14194 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2370 sg2796

lemma sg14195 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2997

lemma sg14196 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg2293 sg2981

lemma sg14197 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg2300 sg2971

lemma sg14198 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg2293 sg2987

lemma sg14199 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg2293 sg2988

lemma sg14200 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,2,1] := by
  exact rowSquare_join (by decide) sg2379 sg2789

lemma sg14201 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3] := by
  exact rowSquare_join (by decide) sg2380 sg2789

lemma sg14202 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2293 sg2989

lemma sg14203 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2382 sg2790

lemma sg14204 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2371 sg2797

lemma sg14205 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2382 sg2791

lemma sg14206 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2384 sg2790

lemma sg14207 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2293 sg2994

lemma sg14208 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2382 sg2793

lemma sg14209 : RowSquare [5,5,2,2,2,2,2,2,2,2,1] [6,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1488 sg3998

lemma sg14210 : RowSquare [5,5,2,2,2,2,2,2,2,2,1] [7,7,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1488 sg4000

lemma sg14211 : RowSquare [5,5,2,2,2,2,2,2,2,2,1] [7,7,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1488 sg4001

lemma sg14212 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1874 sg3614

lemma sg14213 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1880 sg3614

lemma sg14214 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1876 sg3615

lemma sg14215 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1499 sg4415

lemma sg14216 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2371 sg2742

lemma sg14217 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2371 sg2743

lemma sg14218 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1499 sg4417

lemma sg14219 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1876 sg3620

lemma sg14220 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg2279 sg2960

lemma sg14221 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg2373 sg2743

lemma sg14222 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2374 sg2742

lemma sg14223 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2374 sg2743

lemma sg14224 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg4986

lemma sg14225 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2290 sg2908

lemma sg14226 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg2279 sg2961

lemma sg14227 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,3] := by
  exact rowSquare_join (by decide) sg1501 sg4416

lemma sg14228 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg2279 sg2962

lemma sg14229 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,2] := by
  exact rowSquare_join (by decide) sg1501 sg4417

lemma sg14230 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg1502 sg4417

lemma sg14231 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg4988

lemma sg14232 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2281 sg2959

lemma sg14233 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg2293 sg2906

lemma sg14234 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1000 sg4987

lemma sg14235 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg4989

lemma sg14236 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1001 sg4987

lemma sg14237 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2372 sg2745

lemma sg14238 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2372 sg2746

lemma sg14239 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg4988

lemma sg14240 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg2293 sg2907

lemma sg14241 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,3,3] := by
  exact rowSquare_join (by decide) sg2373 sg2746

lemma sg14242 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2374 sg2745

lemma sg14243 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,2] := by
  exact rowSquare_join (by decide) sg2374 sg2746

lemma sg14244 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2282 sg2959

lemma sg14245 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg4988

lemma sg14246 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg2293 sg2908

lemma sg14247 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,2] := by
  exact rowSquare_join (by decide) sg2281 sg2961

lemma sg14248 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,4,1] := by
  exact rowSquare_join (by decide) sg2281 sg2962

lemma sg14249 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,5] := by
  exact rowSquare_join (by decide) sg1001 sg4989

lemma sg14250 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,3] := by
  exact rowSquare_join (by decide) sg1878 sg3620

lemma sg14251 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg2282 sg2960

lemma sg14252 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,2] := by
  exact rowSquare_join (by decide) sg2373 sg2748

lemma sg14253 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,3,1] := by
  exact rowSquare_join (by decide) sg2373 sg2749

lemma sg14254 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,4] := by
  exact rowSquare_join (by decide) sg2374 sg2749

lemma sg14255 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,1] := by
  exact rowSquare_join (by decide) sg2282 sg2961

lemma sg14256 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,3] := by
  exact rowSquare_join (by decide) sg2297 sg2908

lemma sg14257 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1945 sg3470

lemma sg14258 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2376 sg2742

lemma sg14259 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2369 sg2752

lemma sg14260 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2376 sg2743

lemma sg14261 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2290 sg2910

lemma sg14262 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2290 sg2911

lemma sg14263 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1947 sg3470

lemma sg14264 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1948 sg3470

lemma sg14265 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2377 sg2742

lemma sg14266 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2370 sg2752

lemma sg14267 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2377 sg2743

lemma sg14268 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2371 sg2751

lemma sg14269 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2371 sg2752

lemma sg14270 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2378 sg2743

lemma sg14271 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2290 sg2914

lemma sg14272 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2290 sg2915

lemma sg14273 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg2279 sg2967

lemma sg14274 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg2379 sg2743

lemma sg14275 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2380 sg2742

lemma sg14276 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2380 sg2743

lemma sg14277 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1876 sg3624

lemma sg14278 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2290 sg2916

lemma sg14279 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2290 sg2917

lemma sg14280 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2377 sg2745

lemma sg14281 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2377 sg2746

lemma sg14282 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2382 sg2743

lemma sg14283 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2371 sg2754

lemma sg14284 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2279 sg2973

lemma sg14285 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2290 sg2918

lemma sg14286 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2290 sg2919

lemma sg14287 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg2279 sg2974

lemma sg14288 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2279 sg2975

lemma sg14289 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2290 sg2921

lemma sg14290 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg2279 sg2977

lemma sg14291 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,5,2,2] := by
  exact rowSquare_join (by decide) sg2379 sg2748

lemma sg14292 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,5,3,1] := by
  exact rowSquare_join (by decide) sg2281 sg2971

lemma sg14293 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,5,4] := by
  exact rowSquare_join (by decide) sg2380 sg2749

lemma sg14294 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2382 sg2746

lemma sg14295 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2371 sg2755

lemma sg14296 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,3,3,3] := by
  exact rowSquare_join (by decide) sg2383 sg2746

lemma sg14297 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2297 sg2917

lemma sg14298 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg2293 sg2918

lemma sg14299 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2293 sg2919

lemma sg14300 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2371 sg2756

lemma sg14301 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg2293 sg2920

lemma sg14302 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg2293 sg2921

lemma sg14303 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,2,1] := by
  exact rowSquare_join (by decide) sg2281 sg2977

lemma sg14304 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,3] := by
  exact rowSquare_join (by decide) sg2297 sg2919

lemma sg14305 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2377 sg2755

lemma sg14306 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2293 sg2924

lemma sg14307 : RowSquare [5,5,3,2,2,2,2,2,2,1,1] [7,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1084 sg4832

lemma sg14308 : RowSquare [5,5,3,2,2,2,2,2,2,1,1] [7,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1086 sg4832

lemma sg14309 : RowSquare [5,5,3,2,2,2,2,2,2,1,1] [7,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1476 sg3998

lemma sg14310 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1] [4,4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1688 sg3614

lemma sg14311 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1] [5,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1688 sg3615

lemma sg14312 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1] [5,5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1688 sg3617

lemma sg14313 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1] [5,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg1688 sg3620

lemma sg14314 : RowSquare [6,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg1908 sg3577

lemma sg14315 : RowSquare [6,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1758 sg3738

lemma sg14316 : RowSquare [6,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1332 sg4507

lemma sg14317 : RowSquare [6,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1757 sg3731

lemma sg14318 : RowSquare [6,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg4508

lemma sg14319 : RowSquare [6,4,3,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg3501

lemma sg14320 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2289 sg2891

lemma sg14321 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg2273 sg2962

lemma sg14322 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2291 sg2891

lemma sg14323 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1782 sg3671

lemma sg14324 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2894

lemma sg14325 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1758 sg3722

lemma sg14326 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2297 sg2889

lemma sg14327 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg2372 sg2723

lemma sg14328 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2372 sg2724

lemma sg14329 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,4,3,2] := by
  exact rowSquare_join (by decide) sg2295 sg2891

lemma sg14330 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,1] := by
  exact rowSquare_join (by decide) sg2296 sg2891

lemma sg14331 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg2297 sg2890

lemma sg14332 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,2] := by
  exact rowSquare_join (by decide) sg2373 sg2723

lemma sg14333 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,3,1] := by
  exact rowSquare_join (by decide) sg2373 sg2724

lemma sg14334 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,4] := by
  exact rowSquare_join (by decide) sg2374 sg2724

lemma sg14335 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2369 sg2726

lemma sg14336 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2898

lemma sg14337 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2370 sg2726

lemma sg14338 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2289 sg2893

lemma sg14339 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2371 sg2726

lemma sg14340 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2299 sg2891

lemma sg14341 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2273 sg2968

lemma sg14342 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2273 sg2970

lemma sg14343 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,3,2] := by
  exact rowSquare_join (by decide) sg2368 sg2783

lemma sg14344 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg2368 sg2784

lemma sg14345 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2291 sg2893

lemma sg14346 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2273 sg2972

lemma sg14347 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2292 sg2893

lemma sg14348 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2273 sg2973

lemma sg14349 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2273 sg2975

lemma sg14350 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2273 sg2976

lemma sg14351 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,4,3,2] := by
  exact rowSquare_join (by decide) sg2295 sg2893

lemma sg14352 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,4,4,1] := by
  exact rowSquare_join (by decide) sg2296 sg2893

lemma sg14353 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,5,2,2] := by
  exact rowSquare_join (by decide) sg2379 sg2723

lemma sg14354 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,5,3,1] := by
  exact rowSquare_join (by decide) sg2379 sg2724

lemma sg14355 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,5,4] := by
  exact rowSquare_join (by decide) sg2380 sg2724

lemma sg14356 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,3,3,2] := by
  exact rowSquare_join (by decide) sg2303 sg2891

lemma sg14357 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg2304 sg2890

lemma sg14358 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1883 sg3572

lemma sg14359 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2900

lemma sg14360 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2370 sg2733

lemma sg14361 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2305 sg2891

lemma sg14362 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg1782 sg3678

lemma sg14363 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,2,1] := by
  exact rowSquare_join (by decide) sg2297 sg2894

lemma sg14364 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,3] := by
  exact rowSquare_join (by decide) sg2297 sg2895

lemma sg14365 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2372 sg2735

lemma sg14366 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,5,1,1] := by
  exact rowSquare_join (by decide) sg2373 sg2735

lemma sg14367 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,5,2] := by
  exact rowSquare_join (by decide) sg2374 sg2735

lemma sg14368 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2308 sg2889

lemma sg14369 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2375 sg2726

lemma sg14370 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2376 sg2726

lemma sg14371 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2290 sg2897

lemma sg14372 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2290 sg2898

lemma sg14373 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg2273 sg2981

lemma sg14374 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2370 sg2737

lemma sg14375 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2377 sg2726

lemma sg14376 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2273 sg2983

lemma sg14377 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg2293 sg2897

lemma sg14378 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg2273 sg2984

lemma sg14379 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2273 sg2985

lemma sg14380 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2272 sg2988

lemma sg14381 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg2273 sg2988

lemma sg14382 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2301 sg2893

lemma sg14383 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2273 sg2989

lemma sg14384 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2273 sg2990

lemma sg14385 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2368 sg2792

lemma sg14386 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,1] := by
  exact rowSquare_join (by decide) sg2368 sg2793

lemma sg14387 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,2] := by
  exact rowSquare_join (by decide) sg2368 sg2794

lemma sg14388 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg2367 sg2795

lemma sg14389 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2377 sg2731

lemma sg14390 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2377 sg2733

lemma sg14391 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2273 sg2994

lemma sg14392 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,2] := by
  exact rowSquare_join (by decide) sg2306 sg2893

lemma sg14393 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2370 sg2739

lemma sg14394 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2382 sg2731

lemma sg14395 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2293 sg2900

lemma sg14396 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2382 sg2733

lemma sg14397 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1883 sg3589

lemma sg14398 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg2300 sg2897

lemma sg14399 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2273 sg2998

lemma sg14400 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2273 sg2999

lemma sg14401 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2368 sg2797

lemma sg14402 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2901

lemma sg14403 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2388 sg2731

lemma sg14404 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2382 sg2739

lemma sg14405 : RowSquare [6,5,2,2,2,2,2,2,2,1,1] [4,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg656 sg5672

lemma sg14406 : RowSquare [6,5,2,2,2,2,2,2,2,1,1] [6,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg663 sg5672

lemma sg14407 : RowSquare [6,5,2,2,2,2,2,2,2,1,1] [6,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg664 sg5672

lemma sg14408 : RowSquare [6,5,2,2,2,2,2,2,2,1,1] [6,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg665 sg5672

lemma sg14409 : RowSquare [6,5,2,2,2,2,2,2,2,1,1] [6,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg666 sg5672

lemma sg14410 : RowSquare [6,5,2,2,2,2,2,2,2,1,1] [7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg667 sg5672

lemma sg14411 : RowSquare [6,5,2,2,2,2,2,2,2,1,1] [7,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg668 sg5672

lemma sg14412 : RowSquare [6,5,2,2,2,2,2,2,2,1,1] [7,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg663 sg5673

lemma sg14413 : RowSquare [6,5,2,2,2,2,2,2,2,1,1] [7,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg664 sg5673

lemma sg14414 : RowSquare [6,5,2,2,2,2,2,2,2,1,1] [7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg669 sg5672

lemma sg14415 : RowSquare [6,5,2,2,2,2,2,2,2,1,1] [7,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg665 sg5673

lemma sg14416 : RowSquare [6,5,2,2,2,2,2,2,2,1,1] [7,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg666 sg5673

lemma sg14417 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1758 sg3689

lemma sg14418 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1332 sg4487

lemma sg14419 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg1331 sg4488

lemma sg14420 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg1758 sg3690

lemma sg14421 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg1332 sg4488

lemma sg14422 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1758 sg3691

lemma sg14423 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1332 sg4489

lemma sg14424 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg1873 sg3620

lemma sg14425 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg1331 sg4490

lemma sg14426 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1758 sg3697

lemma sg14427 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1332 sg4492

lemma sg14428 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg4496

lemma sg14429 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1757 sg3698

lemma sg14430 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg1331 sg4493

lemma sg14431 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg1758 sg3698

lemma sg14432 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,2] := by
  exact rowSquare_join (by decide) sg1765 sg3690

lemma sg14433 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,4,1] := by
  exact rowSquare_join (by decide) sg1765 sg3691

lemma sg14434 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,5] := by
  exact rowSquare_join (by decide) sg1001 sg4958

lemma sg14435 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg4496

lemma sg14436 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg4961

lemma sg14437 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg4496

lemma sg14438 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,1] := by
  exact rowSquare_join (by decide) sg1332 sg4496

lemma sg14439 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,3] := by
  exact rowSquare_join (by decide) sg892 sg5000

lemma sg14440 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2454 sg2633

lemma sg14441 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2455 sg2633

lemma sg14442 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2368 sg2746

lemma sg14443 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1338 sg4492

lemma sg14444 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,1] := by
  exact rowSquare_join (by decide) sg1340 sg4496

lemma sg14445 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2167 sg3108

lemma sg14446 : RowSquare [6,6,3,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg1332 sg4378

lemma sg14447 : RowSquare [6,6,3,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1332 sg4379

lemma sg14448 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg4303

lemma sg14449 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1675 sg3571

lemma sg14450 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg1332 sg4303

lemma sg14451 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1332 sg4304

lemma sg14452 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1] [6,5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg2135 sg2891

lemma sg14453 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1] [6,6,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg4308

lemma sg14454 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1] [6,6,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1332 sg4308

lemma sg14455 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1] [6,6,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1675 sg3573

lemma sg14456 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1] [7,5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2135 sg2893

lemma sg14457 : RowSquare [7,5,3,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2167 sg2708

lemma sg14458 : RowSquare [7,5,3,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg390 sg6486

lemma sg14459 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2251 sg2626

lemma sg14460 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2251 sg2627

lemma sg14461 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2253 sg2626

lemma sg14462 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2251 sg2628

lemma sg14463 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2254 sg2626

lemma sg14464 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2255 sg2626

lemma sg14465 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg2630

lemma sg14466 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1327 sg4163

lemma sg14467 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2256 sg2626

lemma sg14468 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg2631

lemma sg14469 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1327 sg4164

lemma sg14470 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg2632

lemma sg14471 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg2633

lemma sg14472 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg2634

lemma sg14473 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg2635

lemma sg14474 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2252 sg2633

lemma sg14475 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2261 sg2626

lemma sg14476 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg2637

lemma sg14477 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2253 sg2628

lemma sg14478 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2263 sg2626

lemma sg14479 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg2638

lemma sg14480 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2255 sg2628

lemma sg14481 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2256 sg2628

lemma sg14482 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg2640

lemma sg14483 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2166 sg2702

lemma sg14484 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg4163

lemma sg14485 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg2642

lemma sg14486 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg4163

lemma sg14487 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg2643

lemma sg14488 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1332 sg4163

lemma sg14489 : RowSquare [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2251 sg2879

lemma sg14490 : RowSquare [7,7,2,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2156 sg2707

lemma sg14491 : RowSquare [7,7,2,2,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2158 sg2702

lemma sg14492 : RowSquare [7,7,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2160 sg2702

lemma sg14493 : RowSquare [7,7,4,3,2,2,2] [2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2097 sg2507

lemma sg14494 : RowSquare [7,7,4,3,2,2,2] [2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2152 sg2489

lemma sg14495 : RowSquare [7,7,4,3,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2097 sg2506

lemma sg14496 : RowSquare [7,7,4,3,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2152 sg2488

lemma sg14497 : RowSquare [7,7,4,3,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2097 sg2505

lemma sg14498 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1195 sg4345

lemma sg14499 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [4,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg519 sg5735

lemma sg14500 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg520 sg5735

lemma sg14501 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1645 sg3521

lemma sg14502 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1200 sg4345

lemma sg14503 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1196 sg4350

lemma sg14504 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg521 sg5735

lemma sg14505 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [5,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg522 sg5735

lemma sg14506 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [5,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg523 sg5735

lemma sg14507 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [5,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg519 sg5736

lemma sg14508 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg520 sg5736

lemma sg14509 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [5,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg524 sg5735

lemma sg14510 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg525 sg5735

lemma sg14511 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [6,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg526 sg5735

lemma sg14512 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg521 sg5736

lemma sg14513 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [6,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg527 sg5735

lemma sg14514 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [6,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg522 sg5736

lemma sg14515 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [6,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg528 sg5735

lemma sg14516 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [6,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg523 sg5736

lemma sg14517 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [6,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg529 sg5735

lemma sg14518 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [6,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg524 sg5736

lemma sg14519 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg525 sg5736

lemma sg14520 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg530 sg5735

lemma sg14521 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg531 sg5735

lemma sg14522 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [7,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg532 sg5735

lemma sg14523 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg533 sg5735

lemma sg14524 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [7,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg530 sg5736

lemma sg14525 : RowSquare [8,7,2,1,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1663 sg3522

lemma sg14526 : RowSquare [8,7,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1663 sg3524

lemma sg14527 : RowSquare [8,7,3,2,2,2,2,1] [2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2097 sg2541

lemma sg14528 : RowSquare [8,7,3,2,2,2,2,1] [2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2097 sg2540

lemma sg14529 : RowSquare [8,7,3,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2097 sg2539

lemma sg14530 : RowSquare [8,7,3,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2097 sg2537

lemma sg14531 : RowSquare [8,7,3,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2097 sg2536

lemma sg14532 : RowSquare [8,7,3,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2097 sg2535

lemma sg14533 : RowSquare [8,7,3,2,2,2,2,1] [3,3,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2091 sg2538

lemma sg14534 : RowSquare [8,7,3,2,2,2,2,1] [3,3,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2091 sg2537

lemma sg14535 : RowSquare [8,7,3,2,2,2,2,1] [3,3,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2091 sg2536

lemma sg14536 : RowSquare [8,7,3,2,2,2,2,1] [3,3,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2091 sg2535

lemma sg14537 : RowSquare [8,7,3,2,2,2,2,1] [4,4,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2078 sg2564

lemma sg14538 : RowSquare [8,7,3,2,2,2,2,1] [4,4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2078 sg2562

lemma sg14539 : RowSquare [9,7,2,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg737 sg4930

end UniversalTensorSquare
end
end

end OAI
