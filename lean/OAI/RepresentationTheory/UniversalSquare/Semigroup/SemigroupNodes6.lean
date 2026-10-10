import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes5

namespace OAI

/-! Semigroup Nodes 6. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2897 : RowSquare [8,2,1,1,1,1] [5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg1331

lemma sg2898 : RowSquare [8,2,1,1,1,1] [5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6 sg1332

lemma sg2899 : RowSquare [8,2,1,1,1,1] [5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg893

lemma sg2900 : RowSquare [8,2,1,1,1,1] [5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg897

lemma sg2901 : RowSquare [8,2,1,1,1,1] [7,7] := by
  exact rowSquare_join (by decide) sg17 sg909

lemma sg2902 : RowSquare [8,2,2,1,1] [2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg586

lemma sg2903 : RowSquare [8,2,2,1,1] [3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg586

lemma sg2904 : RowSquare [8,2,2,1,1] [3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg587

lemma sg2905 : RowSquare [8,2,2,1,1] [3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg34 sg586

lemma sg2906 : RowSquare [8,2,2,1,1] [3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg588

lemma sg2907 : RowSquare [8,2,2,1,1] [3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg589

lemma sg2908 : RowSquare [8,2,2,1,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg590

lemma sg2909 : RowSquare [8,2,2,1,1] [4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg35 sg586

lemma sg2910 : RowSquare [8,2,2,1,1] [4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg587

lemma sg2911 : RowSquare [8,2,2,1,1] [4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg87 sg312

lemma sg2912 : RowSquare [8,2,2,1,1] [4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg36 sg586

lemma sg2913 : RowSquare [8,2,2,1,1] [4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg34 sg587

lemma sg2914 : RowSquare [8,2,2,1,1] [4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg88 sg312

lemma sg2915 : RowSquare [8,2,2,1,1] [4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg87 sg313

lemma sg2916 : RowSquare [8,2,2,1,1] [4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg87 sg315

lemma sg2917 : RowSquare [8,2,2,1,1] [4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg998

lemma sg2918 : RowSquare [8,2,2,1,1] [4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg88 sg313

lemma sg2919 : RowSquare [8,2,2,1,1] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg595

lemma sg2920 : RowSquare [8,2,2,1,1] [4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg88 sg314

lemma sg2921 : RowSquare [8,2,2,1,1] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg88 sg315

lemma sg2922 : RowSquare [8,2,2,1,1] [4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg89 sg314

lemma sg2923 : RowSquare [8,2,2,1,1] [4,4,4,2] := by
  exact rowSquare_join (by decide) sg89 sg315

lemma sg2924 : RowSquare [8,2,2,1,1] [5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg92 sg313

lemma sg2925 : RowSquare [8,2,2,2] [2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg178

lemma sg2926 : RowSquare [8,2,2,2] [3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg179

lemma sg2927 : RowSquare [8,2,2,2] [3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg180

lemma sg2928 : RowSquare [8,2,2,2] [3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg181

lemma sg2929 : RowSquare [8,2,2,2] [4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg182

lemma sg2930 : RowSquare [8,2,2,2] [4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg179 sg179

lemma sg2931 : RowSquare [8,2,2,2] [4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg179 sg180

lemma sg2932 : RowSquare [8,2,2,2] [4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg179 sg181

lemma sg2933 : RowSquare [8,2,2,2] [4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg66 sg372

lemma sg2934 : RowSquare [8,2,2,2] [4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg66 sg373

lemma sg2935 : RowSquare [8,2,2,2] [4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg185

lemma sg2936 : RowSquare [8,2,2,2] [4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg67 sg371

lemma sg2937 : RowSquare [8,2,2,2] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg180 sg180

lemma sg2938 : RowSquare [8,2,2,2] [4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg371

lemma sg2939 : RowSquare [8,2,2,2] [4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg180 sg181

lemma sg2940 : RowSquare [8,2,2,2] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg67 sg373

lemma sg2941 : RowSquare [8,2,2,2] [4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg68 sg372

lemma sg2942 : RowSquare [8,2,2,2] [4,4,4,2] := by
  exact rowSquare_join (by decide) sg181 sg181

lemma sg2943 : RowSquare [8,2,2,2] [5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg179 sg182

lemma sg2944 : RowSquare [8,2,2,2] [5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg179 sg183

lemma sg2945 : RowSquare [8,2,2,2] [5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg180 sg182

lemma sg2946 : RowSquare [8,2,2,2] [5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg184

lemma sg2947 : RowSquare [8,2,2,2] [5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg182 sg181

lemma sg2948 : RowSquare [8,2,2,2] [5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg185

lemma sg2949 : RowSquare [8,2,2,2] [5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg180 sg183

lemma sg2950 : RowSquare [8,2,2,2] [5,4,3,2] := by
  exact rowSquare_join (by decide) sg181 sg183

lemma sg2951 : RowSquare [8,2,2,2] [5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg71 sg371

lemma sg2952 : RowSquare [8,2,2,2] [5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg180 sg185

lemma sg2953 : RowSquare [8,2,2,2] [5,5,2,2] := by
  exact rowSquare_join (by decide) sg67 sg377

lemma sg2954 : RowSquare [8,2,2,2] [6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg179 sg186

lemma sg2955 : RowSquare [8,2,2,2] [6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg187

lemma sg2956 : RowSquare [8,2,2,2] [6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg188

lemma sg2957 : RowSquare [8,3,1,1,1] [3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg586

lemma sg2958 : RowSquare [8,3,1,1,1] [3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg586

lemma sg2959 : RowSquare [8,3,1,1,1] [3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg998

lemma sg2960 : RowSquare [8,3,1,1,1] [3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg999

lemma sg2961 : RowSquare [8,3,1,1,1] [3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1000

lemma sg2962 : RowSquare [8,3,1,1,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg1001

lemma sg2963 : RowSquare [8,3,1,1,1] [4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg586

lemma sg2964 : RowSquare [8,3,1,1,1] [4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg587

lemma sg2965 : RowSquare [8,3,1,1,1] [4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg586

lemma sg2966 : RowSquare [8,3,1,1,1] [4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg587

lemma sg2967 : RowSquare [8,3,1,1,1] [4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg588

lemma sg2968 : RowSquare [8,3,1,1,1] [4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg312

lemma sg2969 : RowSquare [8,3,1,1,1] [4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg589

lemma sg2970 : RowSquare [8,3,1,1,1] [4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg16 sg915

lemma sg2971 : RowSquare [8,3,1,1,1] [4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg39 sg590

lemma sg2972 : RowSquare [8,3,1,1,1] [4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg912

lemma sg2973 : RowSquare [8,3,1,1,1] [4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg588

lemma sg2974 : RowSquare [8,3,1,1,1] [4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1006

lemma sg2975 : RowSquare [8,3,1,1,1] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg17 sg915

lemma sg2976 : RowSquare [8,3,1,1,1] [4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg313

lemma sg2977 : RowSquare [8,3,1,1,1] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg1008

lemma sg2978 : RowSquare [8,3,1,1,1] [4,4,4,2] := by
  exact rowSquare_join (by decide) sg97 sg315

lemma sg2979 : RowSquare [8,3,1,1,1] [5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg586

lemma sg2980 : RowSquare [8,3,1,1,1] [5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg534

lemma sg2981 : RowSquare [8,3,1,1,1] [5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg98 sg312

lemma sg2982 : RowSquare [8,3,1,1,1] [5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg534

lemma sg2983 : RowSquare [8,3,1,1,1] [5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg99 sg312

lemma sg2984 : RowSquare [8,3,1,1,1] [5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg98 sg313

lemma sg2985 : RowSquare [8,3,1,1,1] [5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg18 sg915

lemma sg2986 : RowSquare [8,3,1,1,1] [5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg316

lemma sg2987 : RowSquare [8,3,1,1,1] [5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg98 sg314

lemma sg2988 : RowSquare [8,3,1,1,1] [5,3,3,3] := by
  exact rowSquare_join (by decide) sg98 sg315

lemma sg2989 : RowSquare [8,3,1,1,1] [5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg535

lemma sg2990 : RowSquare [8,3,1,1,1] [5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg99 sg313

lemma sg2991 : RowSquare [8,3,1,1,1] [5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg39 sg595

lemma sg2992 : RowSquare [8,3,1,1,1] [5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg97 sg317

lemma sg2993 : RowSquare [8,3,1,1,1] [5,4,3,2] := by
  exact rowSquare_join (by decide) sg99 sg315

lemma sg2994 : RowSquare [8,3,1,1,1] [5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg920

lemma sg2995 : RowSquare [8,3,1,1,1] [5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg40 sg595

lemma sg2996 : RowSquare [8,3,1,1,1] [5,5,2,2] := by
  exact rowSquare_join (by decide) sg13 sg1015

lemma sg2997 : RowSquare [8,3,1,1,1] [5,5,3,1] := by
  exact rowSquare_join (by decide) sg97 sg319

lemma sg2998 : RowSquare [8,3,1,1,1] [6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg101 sg312

lemma sg2999 : RowSquare [8,3,1,1,1] [6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg101 sg313

lemma sg3000 : RowSquare [8,3,2,1] [3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg87 sg330

lemma sg3001 : RowSquare [8,3,2,1] [3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg193

lemma sg3002 : RowSquare [8,3,2,1] [3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg88 sg330

lemma sg3003 : RowSquare [8,3,2,1] [3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg194

lemma sg3004 : RowSquare [8,3,2,1] [3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg371

lemma sg3005 : RowSquare [8,3,2,1] [3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg330

lemma sg3006 : RowSquare [8,3,2,1] [3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg195

lemma sg3007 : RowSquare [8,3,2,1] [3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg372

lemma sg3008 : RowSquare [8,3,2,1] [3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg74 sg373

lemma sg3009 : RowSquare [8,3,2,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg616

lemma sg3010 : RowSquare [8,3,2,1] [4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg90 sg330

lemma sg3011 : RowSquare [8,3,2,1] [4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg196

lemma sg3012 : RowSquare [8,3,2,1] [4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg193 sg179

lemma sg3013 : RowSquare [8,3,2,1] [4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg91 sg330

lemma sg3014 : RowSquare [8,3,2,1] [4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg197

lemma sg3015 : RowSquare [8,3,2,1] [4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg193 sg180

lemma sg3016 : RowSquare [8,3,2,1] [4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg198

lemma sg3017 : RowSquare [8,3,2,1] [4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg193 sg181

lemma sg3018 : RowSquare [8,3,2,1] [4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg87 sg333

lemma sg3019 : RowSquare [8,3,2,1] [4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg87 sg334

lemma sg3020 : RowSquare [8,3,2,1] [4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg92 sg330

lemma sg3021 : RowSquare [8,3,2,1] [4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg199

lemma sg3022 : RowSquare [8,3,2,1] [4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg377

lemma sg3023 : RowSquare [8,3,2,1] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg194 sg180

lemma sg3024 : RowSquare [8,3,2,1] [4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg378

lemma sg3025 : RowSquare [8,3,2,1] [4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg194 sg181

lemma sg3026 : RowSquare [8,3,2,1] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg88 sg334

lemma sg3027 : RowSquare [8,3,2,1] [4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg89 sg333

lemma sg3028 : RowSquare [8,3,2,1] [4,4,4,2] := by
  exact rowSquare_join (by decide) sg195 sg181

lemma sg3029 : RowSquare [8,3,2,1] [5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg93 sg330

lemma sg3030 : RowSquare [8,3,2,1] [5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg200

lemma sg3031 : RowSquare [8,3,2,1] [5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg193 sg182

lemma sg3032 : RowSquare [8,3,2,1] [5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg94 sg330

lemma sg3033 : RowSquare [8,3,2,1] [5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg201

lemma sg3034 : RowSquare [8,3,2,1] [5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg193 sg183

lemma sg3035 : RowSquare [8,3,2,1] [5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg194 sg182

lemma sg3036 : RowSquare [8,3,2,1] [5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg193 sg184

lemma sg3037 : RowSquare [8,3,2,1] [5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg218 sg144

lemma sg3038 : RowSquare [8,3,2,1] [5,3,3,3] := by
  exact rowSquare_join (by decide) sg90 sg334

lemma sg3039 : RowSquare [8,3,2,1] [5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg202

lemma sg3040 : RowSquare [8,3,2,1] [5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg193 sg185

lemma sg3041 : RowSquare [8,3,2,1] [5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg194 sg183

lemma sg3042 : RowSquare [8,3,2,1] [5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg194 sg184

lemma sg3043 : RowSquare [8,3,2,1] [5,4,3,2] := by
  exact rowSquare_join (by decide) sg195 sg183

lemma sg3044 : RowSquare [8,3,2,1] [5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg383

lemma sg3045 : RowSquare [8,3,2,1] [5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg194 sg185

lemma sg3046 : RowSquare [8,3,2,1] [5,5,2,2] := by
  exact rowSquare_join (by decide) sg88 sg338

lemma sg3047 : RowSquare [8,3,2,1] [5,5,3,1] := by
  exact rowSquare_join (by decide) sg195 sg185

lemma sg3048 : RowSquare [8,3,2,1] [6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg850

lemma sg3049 : RowSquare [8,3,2,1] [6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg95 sg330

lemma sg3050 : RowSquare [8,3,2,1] [6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg203

lemma sg3051 : RowSquare [8,3,2,1] [6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg193 sg186

lemma sg3052 : RowSquare [8,3,2,1] [6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg218 sg145

lemma sg3053 : RowSquare [8,3,2,1] [6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg204

lemma sg3054 : RowSquare [8,3,2,1] [6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg193 sg187

lemma sg3055 : RowSquare [8,3,2,1] [6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg194 sg186

lemma sg3056 : RowSquare [8,3,2,1] [6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg218 sg147

lemma sg3057 : RowSquare [8,3,2,1] [6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg193 sg188

lemma sg3058 : RowSquare [8,3,2,1] [6,6,1,1] := by
  exact rowSquare_join (by decide) sg88 sg342

lemma sg3059 : RowSquare [8,3,2,1] [7,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg205

lemma sg3060 : RowSquare [8,3,2,1] [7,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg193 sg189

lemma sg3061 : RowSquare [8,3,2,1] [7,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg193 sg190

lemma sg3062 : RowSquare [8,3,2,1] [7,3,2,1,1] := by
  exact rowSquare_join (by decide) sg194 sg189

lemma sg3063 : RowSquare [8,3,2,1] [7,4,1,1,1] := by
  exact rowSquare_join (by decide) sg194 sg190

lemma sg3064 : RowSquare [8,3,2,1] [7,7] := by
  exact rowSquare_join (by decide) sg92 sg342

lemma sg3065 : RowSquare [8,3,2,1] [8,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg206

lemma sg3066 : RowSquare [8,3,2,1] [8,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg193 sg191

lemma sg3067 : RowSquare [8,3,2,1] [8,3,1,1,1] := by
  exact rowSquare_join (by decide) sg194 sg191

lemma sg3068 : RowSquare [8,3,3] [3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg636

lemma sg3069 : RowSquare [8,3,3] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg637

lemma sg3070 : RowSquare [8,3,3] [4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg87 sg348

lemma sg3071 : RowSquare [8,3,3] [4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg33 sg636

lemma sg3072 : RowSquare [8,3,3] [4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg87 sg349

lemma sg3073 : RowSquare [8,3,3] [4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg87 sg350

lemma sg3074 : RowSquare [8,3,3] [4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg88 sg348

lemma sg3075 : RowSquare [8,3,3] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg639

lemma sg3076 : RowSquare [8,3,3] [4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg348

lemma sg3077 : RowSquare [8,3,3] [4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg88 sg349

lemma sg3078 : RowSquare [8,3,3] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg88 sg350

lemma sg3079 : RowSquare [8,3,3] [4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg89 sg349

lemma sg3080 : RowSquare [8,3,3] [4,4,4,2] := by
  exact rowSquare_join (by decide) sg89 sg350

lemma sg3081 : RowSquare [8,3,3] [5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg154 sg218

lemma sg3082 : RowSquare [8,3,3] [5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg154 sg219

lemma sg3083 : RowSquare [8,3,3] [5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg155 sg218

lemma sg3084 : RowSquare [8,3,3] [5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg154 sg220

lemma sg3085 : RowSquare [8,3,3] [5,3,3,3] := by
  exact rowSquare_join (by decide) sg90 sg350

lemma sg3086 : RowSquare [8,3,3] [5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg91 sg348

lemma sg3087 : RowSquare [8,3,3] [5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg155 sg219

lemma sg3088 : RowSquare [8,3,3] [5,4,3,2] := by
  exact rowSquare_join (by decide) sg156 sg219

lemma sg3089 : RowSquare [8,3,3] [5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg92 sg348

lemma sg3090 : RowSquare [8,3,3] [5,5,2,2] := by
  exact rowSquare_join (by decide) sg88 sg352

lemma sg3091 : RowSquare [8,3,3] [5,5,3,1] := by
  exact rowSquare_join (by decide) sg88 sg353

lemma sg3092 : RowSquare [8,3,3] [6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg874

lemma sg3093 : RowSquare [8,3,3] [6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg154 sg221

lemma sg3094 : RowSquare [8,3,3] [6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg154 sg222

lemma sg3095 : RowSquare [8,3,3] [6,3,3,2] := by
  exact rowSquare_join (by decide) sg156 sg221

lemma sg3096 : RowSquare [8,3,3] [6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg154 sg223

lemma sg3097 : RowSquare [8,3,3] [6,4,2,2] := by
  exact rowSquare_join (by decide) sg219 sg158

lemma sg3098 : RowSquare [8,3,3] [6,6,1,1] := by
  exact rowSquare_join (by decide) sg88 sg354

lemma sg3099 : RowSquare [8,4,1,1] [3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1032

lemma sg3100 : RowSquare [8,4,1,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg1033

lemma sg3101 : RowSquare [8,4,1,1] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg17 sg961

lemma sg3102 : RowSquare [8,4,2] [3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg74 sg390

lemma sg3103 : RowSquare [8,4,2] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg644

lemma sg3104 : RowSquare [8,4,2] [4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg975

lemma sg3105 : RowSquare [8,4,2] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg194 sg194

lemma sg3107 : RowSquare [9,1,1,1,1,1] [5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg1330

lemma sg3108 : RowSquare [9,1,1,1,1,1] [5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg7 sg1332

lemma sg3109 : RowSquare [9,1,1,1,1,1] [6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg890

lemma sg3110 : RowSquare [9,2,1,1,1] [4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg586

lemma sg3111 : RowSquare [9,2,1,1,1] [4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg586

lemma sg3112 : RowSquare [9,2,1,1,1] [4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg998

lemma sg3113 : RowSquare [9,2,1,1,1] [4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg999

lemma sg3114 : RowSquare [9,2,1,1,1] [4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg16 sg1001

lemma sg3115 : RowSquare [9,2,1,1,1] [4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg998

lemma sg3116 : RowSquare [9,2,1,1,1] [4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1000

lemma sg3117 : RowSquare [9,2,1,1,1] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg17 sg1001

lemma sg3118 : RowSquare [9,2,1,1,1] [5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg47 sg586

lemma sg3119 : RowSquare [9,2,2,1] [4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg218

lemma sg3120 : RowSquare [9,2,2,1] [4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg219

lemma sg3121 : RowSquare [9,2,2,1] [4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg87 sg371

lemma sg3122 : RowSquare [9,2,2,1] [4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg220

lemma sg3123 : RowSquare [9,2,2,1] [4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg87 sg372

lemma sg3124 : RowSquare [9,2,2,1] [4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg87 sg373

lemma sg3125 : RowSquare [9,2,2,1] [4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg88 sg371

lemma sg3126 : RowSquare [9,2,2,1] [4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg371

lemma sg3127 : RowSquare [9,2,2,1] [4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg88 sg372

lemma sg3128 : RowSquare [9,2,2,1] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg88 sg373

lemma sg3129 : RowSquare [9,2,2,1] [4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg89 sg372

lemma sg3130 : RowSquare [9,2,2,1] [4,4,4,2] := by
  exact rowSquare_join (by decide) sg89 sg373

lemma sg3131 : RowSquare [9,2,2,1] [5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg221

lemma sg3132 : RowSquare [9,2,2,1] [5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg179 sg218

lemma sg3133 : RowSquare [9,2,2,1] [5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg222

lemma sg3134 : RowSquare [9,2,2,1] [5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg179 sg219

lemma sg3135 : RowSquare [9,2,2,1] [5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg180 sg218

lemma sg3136 : RowSquare [9,2,2,1] [5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg220

lemma sg3137 : RowSquare [9,2,2,1] [5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg218 sg181

lemma sg3138 : RowSquare [9,2,2,1] [5,3,3,3] := by
  exact rowSquare_join (by decide) sg90 sg373

lemma sg3139 : RowSquare [9,2,2,1] [5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg223

lemma sg3140 : RowSquare [9,2,2,1] [5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg91 sg371

lemma sg3141 : RowSquare [9,2,2,1] [5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg180 sg219

lemma sg3142 : RowSquare [9,2,2,1] [5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg180 sg220

lemma sg3143 : RowSquare [9,2,2,1] [5,4,3,2] := by
  exact rowSquare_join (by decide) sg181 sg219

lemma sg3144 : RowSquare [9,2,2,1] [5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg92 sg371

lemma sg3145 : RowSquare [9,2,2,1] [6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg179 sg221

lemma sg3146 : RowSquare [9,2,2,1] [6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg218 sg182

lemma sg3147 : RowSquare [9,3,1,1] [4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg228

lemma sg3148 : RowSquare [9,3,1,1] [4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1032

lemma sg3149 : RowSquare [9,3,1,1] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg17 sg1033

lemma sg3150 : RowSquare [9,3,1,1] [5,5,2,2] := by
  exact rowSquare_join (by decide) sg17 sg1040

lemma sg3151 : RowSquare [9,3,2] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg694

lemma sg3152 : RowSquare [9,3,2] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg88 sg390

lemma sg3153 : RowSquare [9,3,2] [5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1063

lemma sg3154 : RowSquare [9,4,1] [5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg424

lemma sg3155 : RowSquare [10,1,1,1,1] [6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg586

lemma sg3156 : RowSquare [10,1,1,1,1] [6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20 sg1001

lemma sg3157 : RowSquare [3,2,2,2,1,1,1,1,1,1] [5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg227 sg389

lemma sg3158 : RowSquare [3,2,2,2,1,1,1,1,1,1] [5,4,4,2] := by
  exact rowSquare_join (by decide) sg227 sg390

lemma sg3159 : RowSquare [3,2,2,2,1,1,1,1,1,1] [5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg228 sg389

lemma sg3160 : RowSquare [3,2,2,2,1,1,1,1,1,1] [5,5,5] := by
  exact rowSquare_join (by decide) sg97 sg696

lemma sg3161 : RowSquare [3,2,2,2,2,2,1,1] [4,4,4,3] := by
  exact rowSquare_join (by decide) sg207 sg358

lemma sg3162 : RowSquare [3,3,1,1,1,1,1,1,1,1,1] [9,3,3] := by
  exact rowSquare_join (by decide) sg220 sg419

lemma sg3163 : RowSquare [3,3,2,1,1,1,1,1,1,1] [5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg218 sg390

lemma sg3164 : RowSquare [3,3,2,1,1,1,1,1,1,1] [5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg87 sg694

lemma sg3165 : RowSquare [3,3,2,1,1,1,1,1,1,1] [5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg219 sg389

lemma sg3166 : RowSquare [3,3,2,1,1,1,1,1,1,1] [5,4,3,3] := by
  exact rowSquare_join (by decide) sg219 sg390

lemma sg3167 : RowSquare [3,3,2,1,1,1,1,1,1,1] [5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg220 sg389

lemma sg3168 : RowSquare [3,3,2,1,1,1,1,1,1,1] [5,4,4,2] := by
  exact rowSquare_join (by decide) sg220 sg390

lemma sg3169 : RowSquare [3,3,2,1,1,1,1,1,1,1] [5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg88 sg694

lemma sg3170 : RowSquare [3,3,2,1,1,1,1,1,1,1] [5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg89 sg694

lemma sg3171 : RowSquare [3,3,2,1,1,1,1,1,1,1] [5,5,3,2] := by
  exact rowSquare_join (by decide) sg88 sg695

lemma sg3172 : RowSquare [3,3,2,1,1,1,1,1,1,1] [5,5,4,1] := by
  exact rowSquare_join (by decide) sg88 sg696

lemma sg3173 : RowSquare [3,3,2,1,1,1,1,1,1,1] [5,5,5] := by
  exact rowSquare_join (by decide) sg89 sg696

lemma sg3174 : RowSquare [3,3,2,1,1,1,1,1,1,1] [6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg193 sg413

lemma sg3175 : RowSquare [3,3,2,1,1,1,1,1,1,1] [6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg193 sg414

lemma sg3176 : RowSquare [3,3,2,1,1,1,1,1,1,1] [6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg194 sg413

lemma sg3177 : RowSquare [3,3,2,1,1,1,1,1,1,1] [6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg193 sg415

lemma sg3178 : RowSquare [3,3,2,1,1,1,1,1,1,1] [6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg92 sg694

lemma sg3179 : RowSquare [3,3,2,2,1,1,1,1,1] [4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg195 sg389

lemma sg3180 : RowSquare [3,3,2,2,1,1,1,1,1] [4,4,4,3] := by
  exact rowSquare_join (by decide) sg195 sg390

lemma sg3181 : RowSquare [3,3,2,2,1,1,1,1,1] [5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg193 sg391

lemma sg3182 : RowSquare [3,3,2,2,1,1,1,1,1] [5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg975

lemma sg3183 : RowSquare [3,3,2,2,2,2,1] [4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg306

lemma sg3184 : RowSquare [3,3,2,2,2,2,1] [4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg306

lemma sg3185 : RowSquare [3,3,2,2,2,2,1] [5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg211 sg306

lemma sg3186 : RowSquare [4,3,1,1,1,1,1,1,1,1] [5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg413

lemma sg3187 : RowSquare [4,3,1,1,1,1,1,1,1,1] [5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg220 sg372

lemma sg3188 : RowSquare [4,3,1,1,1,1,1,1,1,1] [5,4,4,2] := by
  exact rowSquare_join (by decide) sg220 sg373

lemma sg3189 : RowSquare [4,3,1,1,1,1,1,1,1,1] [6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg179 sg413

lemma sg3190 : RowSquare [4,3,1,1,1,1,1,1,1,1] [6,4,4,1] := by
  exact rowSquare_join (by decide) sg181 sg415

lemma sg3191 : RowSquare [4,3,1,1,1,1,1,1,1,1] [6,5,3,1] := by
  exact rowSquare_join (by decide) sg219 sg378

lemma sg3192 : RowSquare [4,3,1,1,1,1,1,1,1,1] [6,5,4] := by
  exact rowSquare_join (by decide) sg220 sg378

lemma sg3193 : RowSquare [4,3,1,1,1,1,1,1,1,1] [7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg940

lemma sg3194 : RowSquare [4,3,1,1,1,1,1,1,1,1] [7,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg419

lemma sg3195 : RowSquare [4,3,1,1,1,1,1,1,1,1] [7,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg417

lemma sg3196 : RowSquare [4,3,2,1,1,1,1,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg1033

lemma sg3197 : RowSquare [4,3,2,1,1,1,1,1,1] [4,4,4,3] := by
  exact rowSquare_join (by decide) sg195 sg373

lemma sg3198 : RowSquare [4,3,2,1,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg849

lemma sg3199 : RowSquare [4,3,2,2,1,1,1,1] [5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg47 sg849

lemma sg3200 : RowSquare [4,3,2,2,2,1,1] [4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg849

lemma sg3201 : RowSquare [4,3,2,2,2,1,1] [4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg850

lemma sg3202 : RowSquare [4,3,2,2,2,1,1] [4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg849

lemma sg3203 : RowSquare [4,3,2,2,2,1,1] [4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg850

lemma sg3204 : RowSquare [4,3,2,2,2,1,1] [5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg849

lemma sg3205 : RowSquare [4,3,2,2,2,1,1] [6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg849

lemma sg3206 : RowSquare [4,3,3,2,1,1,1] [2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg849

lemma sg3207 : RowSquare [4,3,3,2,1,1,1] [3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg849

lemma sg3208 : RowSquare [4,3,3,2,1,1,1] [3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg34 sg849

lemma sg3209 : RowSquare [4,4,1,1,1,1,1,1,1] [3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg371

lemma sg3210 : RowSquare [4,4,1,1,1,1,1,1,1] [3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg373

lemma sg3211 : RowSquare [4,4,1,1,1,1,1,1,1] [4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg374

lemma sg3212 : RowSquare [4,4,1,1,1,1,1,1,1] [4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg375

lemma sg3213 : RowSquare [4,4,1,1,1,1,1,1,1] [4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg179 sg371

lemma sg3214 : RowSquare [4,4,1,1,1,1,1,1,1] [4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg377

lemma sg3215 : RowSquare [4,4,1,1,1,1,1,1,1] [4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg180 sg371

lemma sg3216 : RowSquare [4,4,1,1,1,1,1,1,1] [4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg378

lemma sg3217 : RowSquare [4,4,1,1,1,1,1,1,1] [4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg181 sg371

lemma sg3218 : RowSquare [4,4,1,1,1,1,1,1,1] [4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg180 sg372

lemma sg3219 : RowSquare [4,4,1,1,1,1,1,1,1] [4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg180 sg373

lemma sg3220 : RowSquare [4,4,1,1,1,1,1,1,1] [4,4,4,3] := by
  exact rowSquare_join (by decide) sg181 sg373

lemma sg3221 : RowSquare [4,4,1,1,1,1,1,1,1] [5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg179 sg374

lemma sg3222 : RowSquare [4,4,1,1,1,1,1,1,1] [5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg182 sg373

lemma sg3223 : RowSquare [4,4,1,1,1,1,1,1,1] [5,4,3,3] := by
  exact rowSquare_join (by decide) sg183 sg373

lemma sg3224 : RowSquare [4,4,1,1,1,1,1,1,1] [5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg383

lemma sg3225 : RowSquare [4,4,1,1,1,1,1,1,1] [6,3,3,3] := by
  exact rowSquare_join (by decide) sg186 sg373

lemma sg3226 : RowSquare [4,4,1,1,1,1,1,1,1] [8,7] := by
  exact rowSquare_join (by decide) sg188 sg383

lemma sg3227 : RowSquare [4,4,1,1,1,1,1,1,1] [9,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg1123

lemma sg3228 : RowSquare [4,4,1,1,1,1,1,1,1] [9,6] := by
  exact rowSquare_join (by decide) sg14 sg1122

lemma sg3229 : RowSquare [4,4,1,1,1,1,1,1,1] [10,5] := by
  exact rowSquare_join (by decide) sg14 sg1124

lemma sg3230 : RowSquare [4,4,1,1,1,1,1,1,1] [11,4] := by
  exact rowSquare_join (by decide) sg14 sg1125

lemma sg3231 : RowSquare [4,4,1,1,1,1,1,1,1] [13,2] := by
  exact rowSquare_join (by decide) sg85 sg427

lemma sg3232 : RowSquare [4,4,2,1,1,1,1,1] [2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg330

lemma sg3233 : RowSquare [4,4,2,1,1,1,1,1] [6,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg2035

lemma sg3234 : RowSquare [4,4,2,1,1,1,1,1] [8,7] := by
  exact rowSquare_join (by decide) sg14 sg1127

lemma sg3235 : RowSquare [4,4,2,1,1,1,1,1] [9,6] := by
  exact rowSquare_join (by decide) sg29 sg722

lemma sg3236 : RowSquare [4,4,2,1,1,1,1,1] [10,5] := by
  exact rowSquare_join (by decide) sg29 sg724

lemma sg3237 : RowSquare [4,4,2,1,1,1,1,1] [11,4] := by
  exact rowSquare_join (by decide) sg29 sg725

lemma sg3238 : RowSquare [4,4,2,1,1,1,1,1] [13,2] := by
  exact rowSquare_join (by decide) sg176 sg235

lemma sg3240 : RowSquare [4,4,2,2,1,1,1] [5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg302

lemma sg3241 : RowSquare [4,4,2,2,1,1,1] [5,5,5] := by
  exact rowSquare_join (by decide) sg97 sg484

lemma sg3242 : RowSquare [4,4,2,2,1,1,1] [6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg1655

lemma sg3243 : RowSquare [4,4,2,2,2,1] [4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg1650

lemma sg3244 : RowSquare [4,4,2,2,2,1] [5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg1651

lemma sg3245 : RowSquare [4,4,2,2,2,1] [5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg1656

lemma sg3246 : RowSquare [4,4,2,2,2,1] [6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg1655

lemma sg3247 : RowSquare [4,4,2,2,2,1] [6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg1657

lemma sg3248 : RowSquare [4,4,2,2,2,1] [7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg1657

lemma sg3249 : RowSquare [4,4,3,2,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg796

lemma sg3250 : RowSquare [4,4,3,2,2] [4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg2111

lemma sg3251 : RowSquare [4,4,4,3] [2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg130 sg257

lemma sg3252 : RowSquare [4,4,4,3] [3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg125 sg259

lemma sg3253 : RowSquare [4,4,4,3] [3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg124 sg259

lemma sg3254 : RowSquare [4,4,4,3] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg129 sg256

lemma sg3255 : RowSquare [5,3,1,1,1,1,1,1,1] [3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg88 sg586

lemma sg3256 : RowSquare [5,3,1,1,1,1,1,1,1] [3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg998

lemma sg3257 : RowSquare [5,3,1,1,1,1,1,1,1] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg586

lemma sg3258 : RowSquare [5,3,1,1,1,1,1,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg1001

lemma sg3259 : RowSquare [5,3,2,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg910

lemma sg3260 : RowSquare [5,3,2,1,1,1,1,1] [2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg586

lemma sg3261 : RowSquare [5,3,2,1,1,1,1,1] [3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg910

lemma sg3262 : RowSquare [5,3,2,1,1,1,1,1] [3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg587

lemma sg3263 : RowSquare [5,3,2,1,1,1,1,1] [3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg588

lemma sg3264 : RowSquare [5,3,2,1,1,1,1,1] [3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg589

lemma sg3265 : RowSquare [5,3,2,1,1,1,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg915

lemma sg3266 : RowSquare [5,3,2,1,1,1,1,1] [4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg1682

lemma sg3267 : RowSquare [5,3,2,1,1,1,1,1] [4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg36 sg910

lemma sg3268 : RowSquare [5,3,2,1,1,1,1,1] [4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg2529

lemma sg3269 : RowSquare [5,3,2,1,1,1,1,1] [5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg2532

lemma sg3270 : RowSquare [5,3,2,1,1,1,1,1] [5,5,5] := by
  exact rowSquare_join (by decide) sg4 sg1586

lemma sg3271 : RowSquare [5,3,2,2,1,1,1] [3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg910

lemma sg3272 : RowSquare [5,3,2,2,1,1,1] [3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg27 sg910

lemma sg3273 : RowSquare [5,3,2,2,1,1,1] [6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2542

lemma sg3274 : RowSquare [5,4,1,1,1,1,1,1] [3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg66 sg586

lemma sg3275 : RowSquare [5,4,1,1,1,1,1,1] [3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg2546

lemma sg3276 : RowSquare [5,4,1,1,1,1,1,1] [3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg67 sg586

lemma sg3277 : RowSquare [5,4,1,1,1,1,1,1] [3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg313

lemma sg3278 : RowSquare [5,4,1,1,1,1,1,1] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg586

lemma sg3279 : RowSquare [5,4,1,1,1,1,1,1] [3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg315

lemma sg3280 : RowSquare [5,4,1,1,1,1,1,1] [4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg69 sg586

lemma sg3281 : RowSquare [5,4,1,1,1,1,1,1] [4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg66 sg587

lemma sg3282 : RowSquare [5,4,1,1,1,1,1,1] [4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg70 sg586

lemma sg3283 : RowSquare [5,4,1,1,1,1,1,1] [4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg67 sg587

lemma sg3284 : RowSquare [5,4,1,1,1,1,1,1] [4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg179 sg313

lemma sg3285 : RowSquare [5,4,1,1,1,1,1,1] [4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg587

lemma sg3286 : RowSquare [5,4,1,1,1,1,1,1] [4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg66 sg590

lemma sg3287 : RowSquare [5,4,1,1,1,1,1,1] [4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg71 sg586

lemma sg3288 : RowSquare [5,4,1,1,1,1,1,1] [4,4,4,3] := by
  exact rowSquare_join (by decide) sg181 sg315

lemma sg3289 : RowSquare [5,4,1,1,1,1,1,1] [5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg69 sg587

lemma sg3290 : RowSquare [5,4,1,1,1,1,1,1] [6,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg1137

lemma sg3291 : RowSquare [5,4,1,1,1,1,1,1] [7,6,2] := by
  exact rowSquare_join (by decide) sg14 sg1139

lemma sg3292 : RowSquare [5,4,1,1,1,1,1,1] [8,7] := by
  exact rowSquare_join (by decide) sg14 sg1141

lemma sg3293 : RowSquare [5,4,2,1,1,1,1] [4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg22 sg910

lemma sg3294 : RowSquare [5,4,2,1,1,1,1] [4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg2074

lemma sg3295 : RowSquare [5,4,2,1,1,1,1] [4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg23 sg910

lemma sg3296 : RowSquare [5,4,2,1,1,1,1] [5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg24 sg910

lemma sg3297 : RowSquare [5,4,2,1,1,1,1] [6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg2077

lemma sg3298 : RowSquare [5,4,3,1,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg759

end UniversalTensorSquare
end
end

end OAI
