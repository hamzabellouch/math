import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes23
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes30

namespace OAI

/-! Semigroup Nodes 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12940 : RowSquare [8,6,2,2,1,1,1,1,1,1,1,1] [5,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg821 sg4345

lemma sg12941 : RowSquare [8,6,3,2,1,1,1,1,1,1,1] [5,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg260 sg5735

lemma sg12942 : RowSquare [8,6,3,2,1,1,1,1,1,1,1] [5,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg261 sg5735

lemma sg12943 : RowSquare [8,6,3,2,1,1,1,1,1,1,1] [5,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg262 sg5735

lemma sg12944 : RowSquare [8,7,2,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1189 sg3521

lemma sg12945 : RowSquare [8,7,2,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1190 sg3521

lemma sg12946 : RowSquare [8,7,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1191 sg3521

lemma sg12947 : RowSquare [8,7,2,2,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg740 sg4345

lemma sg12948 : RowSquare [8,7,2,2,2,2,2,1] [2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2099 sg2072

lemma sg12949 : RowSquare [8,7,2,2,2,2,2,1] [2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2097 sg2072

lemma sg12950 : RowSquare [8,7,2,2,2,2,2,1] [2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2097 sg2071

lemma sg12951 : RowSquare [8,7,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2097 sg2070

lemma sg12952 : RowSquare [8,7,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2097 sg2069

lemma sg12953 : RowSquare [8,7,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2097 sg2068

lemma sg12954 : RowSquare [8,7,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2097 sg2067

lemma sg12955 : RowSquare [8,7,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2097 sg2066

lemma sg12956 : RowSquare [8,7,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1644 sg2566

lemma sg12957 : RowSquare [8,7,2,2,2,2,2,1] [3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2096 sg2072

lemma sg12958 : RowSquare [8,7,2,2,2,2,2,1] [3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2092 sg2072

lemma sg12959 : RowSquare [8,7,2,2,2,2,2,1] [3,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2092 sg2071

lemma sg12960 : RowSquare [8,7,2,2,2,2,2,1] [3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2100 sg2072

lemma sg12961 : RowSquare [8,7,2,2,2,2,2,1] [3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2091 sg2072

lemma sg12962 : RowSquare [8,7,2,2,2,2,2,1] [3,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2091 sg2070

lemma sg12963 : RowSquare [8,7,2,2,2,2,2,1] [3,3,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2091 sg2068

lemma sg12964 : RowSquare [8,7,2,2,2,2,2,1] [3,3,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2091 sg2066

lemma sg12965 : RowSquare [8,7,2,2,2,2,2,1] [3,3,3,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2088 sg2065

lemma sg12966 : RowSquare [8,7,2,2,2,2,2,1] [4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2093 sg2072

lemma sg12967 : RowSquare [8,7,2,2,2,2,2,1] [4,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg995 sg3744

lemma sg12968 : RowSquare [8,7,2,2,2,2,2,1] [4,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg364 sg5115

lemma sg12969 : RowSquare [8,7,2,2,2,2,2,1] [5,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2086 sg2072

lemma sg12970 : RowSquare [8,7,2,2,2,2,2,1] [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2086 sg2070

lemma sg12971 : RowSquare [8,7,2,2,2,2,2,1] [7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg11364

lemma sg12972 : RowSquare [8,7,2,2,2,2,2,1] [7,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11365

lemma sg12973 : RowSquare [8,7,2,2,2,2,2,1] [7,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11385

lemma sg12974 : RowSquare [8,7,2,2,2,2,2,1] [7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10060

lemma sg12975 : RowSquare [8,7,2,2,2,2,2,1] [7,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg11768

lemma sg12976 : RowSquare [8,7,2,2,2,2,2,1] [7,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg11769

lemma sg12977 : RowSquare [8,7,2,2,2,2,2,1] [7,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg11770

lemma sg12978 : RowSquare [8,7,2,2,2,2,2,1] [7,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg11771

lemma sg12979 : RowSquare [8,7,2,2,2,2,2,1] [7,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg11772

lemma sg12980 : RowSquare [8,7,2,2,2,2,2,1] [7,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg11773

lemma sg12981 : RowSquare [8,7,2,2,2,2,2,1] [7,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10044

lemma sg12982 : RowSquare [8,7,2,2,2,2,2,1] [7,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11386

lemma sg12983 : RowSquare [8,7,2,2,2,2,2,1] [7,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8297

lemma sg12984 : RowSquare [8,7,2,2,2,2,2,1] [7,3,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11366

lemma sg12985 : RowSquare [8,7,2,2,2,2,2,1] [7,3,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11367

lemma sg12986 : RowSquare [8,7,2,2,2,2,2,1] [7,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11368

lemma sg12987 : RowSquare [8,7,2,2,2,2,2,1] [7,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11369

lemma sg12988 : RowSquare [8,7,2,2,2,2,2,1] [7,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11370

lemma sg12989 : RowSquare [8,7,2,2,2,2,2,1] [7,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg11371

lemma sg12990 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg8295

lemma sg12991 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8298

lemma sg12992 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11387

lemma sg12993 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11388

lemma sg12994 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11389

lemma sg12995 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11390

lemma sg12996 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg11391

lemma sg12997 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg6864

lemma sg12998 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10061

lemma sg12999 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10062

lemma sg13000 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10063

lemma sg13001 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10064

lemma sg13002 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg10065

lemma sg13003 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg11774

lemma sg13004 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg11775

lemma sg13005 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg11776

lemma sg13006 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg11777

lemma sg13007 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg11778

lemma sg13008 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg11779

lemma sg13009 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg11780

lemma sg13010 : RowSquare [8,7,2,2,2,2,2,1] [7,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1642 sg2546

lemma sg13011 : RowSquare [8,7,2,2,2,2,2,1] [7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11372

lemma sg13012 : RowSquare [8,7,2,2,2,2,2,1] [7,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8297

lemma sg13013 : RowSquare [8,7,2,2,2,2,2,1] [7,4,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8299

lemma sg13014 : RowSquare [8,7,2,2,2,2,2,1] [7,4,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11373

lemma sg13015 : RowSquare [8,7,2,2,2,2,2,1] [7,4,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11374

lemma sg13016 : RowSquare [8,7,2,2,2,2,2,1] [7,4,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11375

lemma sg13017 : RowSquare [8,7,2,2,2,2,2,1] [7,4,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11376

lemma sg13018 : RowSquare [8,7,2,2,2,2,2,1] [7,4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg11377

lemma sg13019 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8298

lemma sg13020 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8300

lemma sg13021 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11392

lemma sg13022 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11393

lemma sg13023 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11394

lemma sg13024 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11395

lemma sg13025 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg11396

lemma sg13026 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8301

lemma sg13027 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg12659

lemma sg13028 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg12660

lemma sg13029 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg12661

lemma sg13030 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg12662

lemma sg13031 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg12663

lemma sg13032 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg12664

lemma sg13033 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg12665

lemma sg13034 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg12666

lemma sg13035 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg12667

lemma sg13036 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1637 sg2547

lemma sg13037 : RowSquare [8,7,2,2,2,2,2,1] [7,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1643 sg2546

lemma sg13038 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11397

lemma sg13039 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg6865

lemma sg13040 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11398

lemma sg13041 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11399

lemma sg13042 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11400

lemma sg13043 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg11401

lemma sg13044 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5928

lemma sg13045 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8303

lemma sg13046 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8304

lemma sg13047 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8305

lemma sg13048 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg207 sg5929

lemma sg13049 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11402

lemma sg13050 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1149 sg3274

lemma sg13051 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg11403

lemma sg13052 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11404

lemma sg13053 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1638 sg2547

lemma sg13054 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8306

lemma sg13055 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8307

lemma sg13056 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8308

lemma sg13057 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg39 sg8309

lemma sg13058 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1146 sg3280

lemma sg13059 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg12668

lemma sg13060 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg2082 sg2045

lemma sg13061 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1633 sg2550

lemma sg13062 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1146 sg3281

lemma sg13063 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2082 sg2046

lemma sg13064 : RowSquare [8,7,2,2,2,2,2,1] [7,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg8296

lemma sg13065 : RowSquare [8,7,2,2,2,2,2,1] [7,5,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8299

lemma sg13066 : RowSquare [8,7,2,2,2,2,2,1] [7,5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8310

lemma sg13067 : RowSquare [8,7,2,2,2,2,2,1] [7,5,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11378

lemma sg13068 : RowSquare [8,7,2,2,2,2,2,1] [7,5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11379

lemma sg13069 : RowSquare [8,7,2,2,2,2,2,1] [7,5,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11380

lemma sg13070 : RowSquare [8,7,2,2,2,2,2,1] [7,5,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11381

lemma sg13071 : RowSquare [8,7,2,2,2,2,2,1] [7,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg11382

lemma sg13072 : RowSquare [8,7,2,2,2,2,2,1] [7,5,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg6867

lemma sg13073 : RowSquare [8,7,2,2,2,2,2,1] [7,5,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8311

lemma sg13074 : RowSquare [8,7,2,2,2,2,2,1] [7,5,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11405

lemma sg13075 : RowSquare [8,7,2,2,2,2,2,1] [7,5,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11406

lemma sg13076 : RowSquare [8,7,2,2,2,2,2,1] [7,5,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11407

lemma sg13077 : RowSquare [8,7,2,2,2,2,2,1] [7,5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg11408

lemma sg13078 : RowSquare [8,7,2,2,2,2,2,1] [7,5,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg5923

lemma sg13079 : RowSquare [8,7,2,2,2,2,2,1] [7,5,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8312

lemma sg13080 : RowSquare [8,7,2,2,2,2,2,1] [7,5,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8313

lemma sg13081 : RowSquare [8,7,2,2,2,2,2,1] [7,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8314

lemma sg13082 : RowSquare [8,7,2,2,2,2,2,1] [7,5,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg39 sg8315

lemma sg13083 : RowSquare [8,7,2,2,2,2,2,1] [7,5,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11383

lemma sg13084 : RowSquare [8,7,2,2,2,2,2,1] [7,5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1151 sg3274

lemma sg13085 : RowSquare [8,7,2,2,2,2,2,1] [7,5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1637 sg2548

lemma sg13086 : RowSquare [8,7,2,2,2,2,2,1] [7,5,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11384

lemma sg13087 : RowSquare [8,7,2,2,2,2,2,1] [7,5,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1639 sg2547

lemma sg13088 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8302

lemma sg13089 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5930

lemma sg13090 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8303

lemma sg13091 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8304

lemma sg13092 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8305

lemma sg13093 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg83 sg6868

lemma sg13094 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5931

lemma sg13095 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8316

lemma sg13096 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1149 sg3276

lemma sg13097 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1637 sg2549

lemma sg13098 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1146 sg3282

lemma sg13099 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11409

lemma sg13100 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2082 sg2047

lemma sg13101 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1635 sg2550

lemma sg13102 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8317

lemma sg13103 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1147 sg3280

lemma sg13104 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg364 sg5110

lemma sg13105 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg2083 sg2045

lemma sg13106 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1146 sg3283

lemma sg13107 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg2082 sg2048

lemma sg13108 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2082 sg2049

lemma sg13109 : RowSquare [8,7,2,2,2,2,2,1] [7,5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg5924

lemma sg13110 : RowSquare [8,7,2,2,2,2,2,1] [7,5,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5932

lemma sg13111 : RowSquare [8,7,2,2,2,2,2,1] [7,5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11410

lemma sg13112 : RowSquare [8,7,2,2,2,2,2,1] [7,5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1149 sg3278

lemma sg13113 : RowSquare [8,7,2,2,2,2,2,1] [7,5,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg209 sg5925

lemma sg13114 : RowSquare [8,7,2,2,2,2,2,1] [7,5,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg5111

lemma sg13115 : RowSquare [8,7,2,2,2,2,2,1] [7,5,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1150 sg3278

lemma sg13116 : RowSquare [8,7,2,2,2,2,2,1] [7,5,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5933

lemma sg13117 : RowSquare [8,7,2,2,2,2,2,1] [7,5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2085 sg2042

lemma sg13118 : RowSquare [8,7,2,2,2,2,2,1] [7,5,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1146 sg3285

lemma sg13119 : RowSquare [8,7,2,2,2,2,2,1] [7,5,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2082 sg2050

lemma sg13120 : RowSquare [8,7,2,2,2,2,2,1] [7,5,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8318

lemma sg13121 : RowSquare [8,7,2,2,2,2,2,1] [7,5,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg5112

lemma sg13122 : RowSquare [8,7,2,2,2,2,2,1] [7,5,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1633 sg2552

lemma sg13123 : RowSquare [8,7,2,2,2,2,2,1] [7,5,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2082 sg2051

lemma sg13124 : RowSquare [8,7,2,2,2,2,2,1] [7,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg656 sg4566

lemma sg13125 : RowSquare [8,7,2,2,2,2,2,1] [7,6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10045

lemma sg13126 : RowSquare [8,7,2,2,2,2,2,1] [7,6,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8310

lemma sg13127 : RowSquare [8,7,2,2,2,2,2,1] [7,6,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10066

lemma sg13128 : RowSquare [8,7,2,2,2,2,2,1] [7,6,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10046

lemma sg13129 : RowSquare [8,7,2,2,2,2,2,1] [7,6,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10047

lemma sg13130 : RowSquare [8,7,2,2,2,2,2,1] [7,6,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10048

lemma sg13131 : RowSquare [8,7,2,2,2,2,2,1] [7,6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg10049

lemma sg13132 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8311

lemma sg13133 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5934

lemma sg13134 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8312

lemma sg13135 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8313

lemma sg13136 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8314

lemma sg13137 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg40 sg8315

lemma sg13138 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10067

lemma sg13139 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10068

lemma sg13140 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1151 sg3276

lemma sg13141 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg10069

lemma sg13142 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1146 sg3287

lemma sg13143 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2084 sg2063

lemma sg13144 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2082 sg2053

lemma sg13145 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1640 sg2547

lemma sg13146 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg5927

lemma sg13147 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5935

lemma sg13148 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8316

lemma sg13149 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1151 sg3278

lemma sg13150 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg210 sg5925

lemma sg13151 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5936

lemma sg13152 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1147 sg3282

lemma sg13153 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg365 sg5109

lemma sg13154 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2083 sg2047

lemma sg13155 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg5926

lemma sg13156 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2082 sg2054

lemma sg13157 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1153 sg3276

lemma sg13158 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1147 sg3283

lemma sg13159 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg2083 sg2048

lemma sg13160 : RowSquare [8,7,2,2,2,2,2,1] [7,6,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg6869

lemma sg13161 : RowSquare [8,7,2,2,2,2,2,1] [7,6,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5937

lemma sg13162 : RowSquare [8,7,2,2,2,2,2,1] [7,6,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1148 sg3282

lemma sg13163 : RowSquare [8,7,2,2,2,2,2,1] [7,6,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg83 sg6870

lemma sg13164 : RowSquare [8,7,2,2,2,2,2,1] [7,6,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2084 sg2047

lemma sg13165 : RowSquare [8,7,2,2,2,2,2,1] [7,6,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1153 sg3278

lemma sg13166 : RowSquare [8,7,2,2,2,2,2,1] [7,6,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1147 sg3285

lemma sg13167 : RowSquare [8,7,2,2,2,2,2,1] [7,6,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg656 sg4567

lemma sg13168 : RowSquare [8,7,2,2,2,2,2,1] [7,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg6871

lemma sg13169 : RowSquare [8,7,2,2,2,2,2,1] [7,6,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1154 sg3278

lemma sg13170 : RowSquare [8,7,2,2,2,2,2,1] [7,6,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1148 sg3285

lemma sg13171 : RowSquare [8,7,2,2,2,2,2,1] [7,6,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg656 sg4568

lemma sg13172 : RowSquare [8,7,2,2,2,2,2,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10050

lemma sg13173 : RowSquare [8,7,2,2,2,2,2,1] [7,7,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10051

lemma sg13174 : RowSquare [8,7,2,2,2,2,2,1] [7,7,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10070

lemma sg13175 : RowSquare [8,7,2,2,2,2,2,1] [7,7,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10052

lemma sg13176 : RowSquare [8,7,2,2,2,2,2,1] [7,7,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10053

lemma sg13177 : RowSquare [8,7,2,2,2,2,2,1] [7,7,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10054

lemma sg13178 : RowSquare [8,7,2,2,2,2,2,1] [7,7,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg10055

lemma sg13179 : RowSquare [8,7,2,2,2,2,2,1] [7,7,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg5927

lemma sg13180 : RowSquare [8,7,2,2,2,2,2,1] [7,7,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10071

lemma sg13181 : RowSquare [8,7,2,2,2,2,2,1] [7,7,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10056

lemma sg13182 : RowSquare [8,7,2,2,2,2,2,1] [7,7,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10057

lemma sg13183 : RowSquare [8,7,2,2,2,2,2,1] [7,7,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg10058

lemma sg13184 : RowSquare [8,7,2,2,2,2,2,1] [7,7,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg5113

lemma sg13185 : RowSquare [8,7,2,2,2,2,2,1] [7,7,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1147 sg3287

lemma sg13186 : RowSquare [8,7,2,2,2,2,2,1] [7,7,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10072

lemma sg13187 : RowSquare [8,7,2,2,2,2,2,1] [7,7,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2083 sg2053

lemma sg13188 : RowSquare [8,7,2,2,2,2,2,1] [7,7,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10059

lemma sg13189 : RowSquare [8,7,2,2,2,2,2,1] [7,7,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8319

lemma sg13190 : RowSquare [8,7,2,2,2,2,2,1] [7,7,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5938

lemma sg13191 : RowSquare [8,7,2,2,2,2,2,1] [7,7,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1148 sg3287

lemma sg13192 : RowSquare [8,7,2,2,2,2,2,1] [7,7,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg83 sg6872

lemma sg13193 : RowSquare [8,7,2,2,2,2,2,1] [7,7,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1156 sg3276

lemma sg13194 : RowSquare [8,7,2,2,2,2,2,1] [7,7,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10073

lemma sg13195 : RowSquare [8,7,2,2,2,2,2,1] [7,7,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg5114

lemma sg13196 : RowSquare [8,7,2,2,2,2,2,1] [7,7,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg6873

lemma sg13197 : RowSquare [8,7,2,2,2,2,2,1] [7,7,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1156 sg3278

lemma sg13198 : RowSquare [8,7,2,2,2,2,2,1] [7,7,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg6874

lemma sg13199 : RowSquare [8,7,2,2,2,2,2,1] [7,7,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg657 sg4567

lemma sg13200 : RowSquare [8,7,2,2,2,2,2,1] [7,7,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1157 sg3278

lemma sg13201 : RowSquare [8,7,2,2,2,2,2,1] [7,7,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg657 sg4568

lemma sg13202 : RowSquare [8,7,2,2,2,2,2,1] [7,7,7,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg658 sg4568

lemma sg13203 : RowSquare [8,7,2,2,2,2,2,1] [8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg11365

lemma sg13204 : RowSquare [8,7,2,2,2,2,2,1] [8,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11385

lemma sg13205 : RowSquare [8,7,2,2,2,2,2,1] [8,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11411

lemma sg13206 : RowSquare [8,7,2,2,2,2,2,1] [8,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8320

lemma sg13207 : RowSquare [8,7,2,2,2,2,2,1] [8,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg11366

lemma sg13208 : RowSquare [8,7,2,2,2,2,2,1] [8,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg11367

lemma sg13209 : RowSquare [8,7,2,2,2,2,2,1] [8,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg11368

lemma sg13210 : RowSquare [8,7,2,2,2,2,2,1] [8,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg11369

lemma sg13211 : RowSquare [8,7,2,2,2,2,2,1] [8,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6 sg11370

lemma sg13212 : RowSquare [8,7,2,2,2,2,2,1] [8,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6 sg11371

lemma sg13213 : RowSquare [8,7,2,2,2,2,2,1] [8,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10060

lemma sg13214 : RowSquare [8,7,2,2,2,2,2,1] [8,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8320

lemma sg13215 : RowSquare [8,7,2,2,2,2,2,1] [8,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8321

lemma sg13216 : RowSquare [8,7,2,2,2,2,2,1] [8,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11387

lemma sg13217 : RowSquare [8,7,2,2,2,2,2,1] [8,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11388

lemma sg13218 : RowSquare [8,7,2,2,2,2,2,1] [8,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11389

lemma sg13219 : RowSquare [8,7,2,2,2,2,2,1] [8,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11390

lemma sg13220 : RowSquare [8,7,2,2,2,2,2,1] [8,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg11391

lemma sg13221 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg8298

lemma sg13222 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8322

lemma sg13223 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11412

lemma sg13224 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11413

lemma sg13225 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11414

lemma sg13226 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11415

lemma sg13227 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg11416

lemma sg13228 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg6866

lemma sg13229 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10074

lemma sg13230 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10075

lemma sg13231 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10076

lemma sg13232 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg10077

lemma sg13233 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg11781

lemma sg13234 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg11782

lemma sg13235 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg11783

lemma sg13236 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg11784

lemma sg13237 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg11785

lemma sg13238 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1642 sg2547

lemma sg13239 : RowSquare [8,7,2,2,2,2,2,1] [8,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg8297

lemma sg13240 : RowSquare [8,7,2,2,2,2,2,1] [8,4,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8321

lemma sg13241 : RowSquare [8,7,2,2,2,2,2,1] [8,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg6867

lemma sg13242 : RowSquare [8,7,2,2,2,2,2,1] [8,4,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10061

lemma sg13243 : RowSquare [8,7,2,2,2,2,2,1] [8,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10062

lemma sg13244 : RowSquare [8,7,2,2,2,2,2,1] [8,4,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10063

lemma sg13245 : RowSquare [8,7,2,2,2,2,2,1] [8,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10064

lemma sg13246 : RowSquare [8,7,2,2,2,2,2,1] [8,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg10065

lemma sg13247 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8322

lemma sg13248 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8324

lemma sg13249 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11417

lemma sg13250 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11418

lemma sg13251 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11419

lemma sg13252 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg11420

lemma sg13253 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg5928

lemma sg13254 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8325

lemma sg13255 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8326

lemma sg13256 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8327

lemma sg13257 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg208 sg5929

lemma sg13258 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11402

lemma sg13259 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1158 sg3274

lemma sg13260 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2059 sg2082

lemma sg13261 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1637 sg2550

lemma sg13262 : RowSquare [8,7,2,2,2,2,2,1] [8,4,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg8302

lemma sg13263 : RowSquare [8,7,2,2,2,2,2,1] [8,4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5939

lemma sg13264 : RowSquare [8,7,2,2,2,2,2,1] [8,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg8303

lemma sg13265 : RowSquare [8,7,2,2,2,2,2,1] [8,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg8304

lemma sg13266 : RowSquare [8,7,2,2,2,2,2,1] [8,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg41 sg8305

lemma sg13267 : RowSquare [8,7,2,2,2,2,2,1] [8,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg209 sg5929

lemma sg13268 : RowSquare [8,7,2,2,2,2,2,1] [8,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5940

lemma sg13269 : RowSquare [8,7,2,2,2,2,2,1] [8,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8328

lemma sg13270 : RowSquare [8,7,2,2,2,2,2,1] [8,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1149 sg3280

lemma sg13271 : RowSquare [8,7,2,2,2,2,2,1] [8,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1642 sg2549

lemma sg13272 : RowSquare [8,7,2,2,2,2,2,1] [8,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1592 sg2592

lemma sg13273 : RowSquare [8,7,2,2,2,2,2,1] [8,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1149 sg3281

lemma sg13274 : RowSquare [8,7,2,2,2,2,2,1] [8,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg5116

lemma sg13275 : RowSquare [8,7,2,2,2,2,2,1] [8,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1150 sg3280

lemma sg13276 : RowSquare [8,7,2,2,2,2,2,1] [8,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg364 sg5117

lemma sg13277 : RowSquare [8,7,2,2,2,2,2,1] [8,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1146 sg3289

lemma sg13278 : RowSquare [8,7,2,2,2,2,2,1] [8,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg8299

lemma sg13279 : RowSquare [8,7,2,2,2,2,2,1] [8,5,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8323

lemma sg13280 : RowSquare [8,7,2,2,2,2,2,1] [8,5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8329

lemma sg13281 : RowSquare [8,7,2,2,2,2,2,1] [8,5,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11405

lemma sg13282 : RowSquare [8,7,2,2,2,2,2,1] [8,5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11406

lemma sg13283 : RowSquare [8,7,2,2,2,2,2,1] [8,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg11407

lemma sg13284 : RowSquare [8,7,2,2,2,2,2,1] [8,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg11408

lemma sg13285 : RowSquare [8,7,2,2,2,2,2,1] [8,5,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg6875

lemma sg13286 : RowSquare [8,7,2,2,2,2,2,1] [8,5,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5941

lemma sg13287 : RowSquare [8,7,2,2,2,2,2,1] [8,5,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8325

lemma sg13288 : RowSquare [8,7,2,2,2,2,2,1] [8,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8326

lemma sg13289 : RowSquare [8,7,2,2,2,2,2,1] [8,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8327

lemma sg13290 : RowSquare [8,7,2,2,2,2,2,1] [8,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg210 sg5929

lemma sg13291 : RowSquare [8,7,2,2,2,2,2,1] [8,5,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg5931

lemma sg13292 : RowSquare [8,7,2,2,2,2,2,1] [8,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg8330

lemma sg13293 : RowSquare [8,7,2,2,2,2,2,1] [8,5,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1151 sg3280

lemma sg13294 : RowSquare [8,7,2,2,2,2,2,1] [8,5,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2059 sg2083

lemma sg13295 : RowSquare [8,7,2,2,2,2,2,1] [8,5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1592 sg2593

lemma sg13296 : RowSquare [8,7,2,2,2,2,2,1] [8,5,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1637 sg2551

lemma sg13297 : RowSquare [8,7,2,2,2,2,2,1] [8,5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg5930

lemma sg13298 : RowSquare [8,7,2,2,2,2,2,1] [8,5,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5942

lemma sg13299 : RowSquare [8,7,2,2,2,2,2,1] [8,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8328

lemma sg13300 : RowSquare [8,7,2,2,2,2,2,1] [8,5,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1149 sg3282

lemma sg13301 : RowSquare [8,7,2,2,2,2,2,1] [8,5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2059 sg2084

lemma sg13302 : RowSquare [8,7,2,2,2,2,2,1] [8,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5943

lemma sg13303 : RowSquare [8,7,2,2,2,2,2,1] [8,5,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1593 sg2592

lemma sg13304 : RowSquare [8,7,2,2,2,2,2,1] [8,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1637 sg2552

lemma sg13305 : RowSquare [8,7,2,2,2,2,2,1] [8,5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1637 sg2553

lemma sg13306 : RowSquare [8,7,2,2,2,2,2,1] [8,5,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1153 sg3280

lemma sg13307 : RowSquare [8,7,2,2,2,2,2,1] [8,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1637 sg2554

lemma sg13308 : RowSquare [8,7,2,2,2,2,2,1] [8,5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg5932

lemma sg13309 : RowSquare [8,7,2,2,2,2,2,1] [8,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5944

lemma sg13310 : RowSquare [8,7,2,2,2,2,2,1] [8,5,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1594 sg2592

lemma sg13311 : RowSquare [8,7,2,2,2,2,2,1] [8,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1149 sg3285

lemma sg13312 : RowSquare [8,7,2,2,2,2,2,1] [8,5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1160 sg3278

lemma sg13313 : RowSquare [8,7,2,2,2,2,2,1] [8,6,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg8310

lemma sg13314 : RowSquare [8,7,2,2,2,2,2,1] [8,6,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8329

lemma sg13315 : RowSquare [8,7,2,2,2,2,2,1] [8,6,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg5934

lemma sg13316 : RowSquare [8,7,2,2,2,2,2,1] [8,6,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg8312

lemma sg13317 : RowSquare [8,7,2,2,2,2,2,1] [8,6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg8313

lemma sg13318 : RowSquare [8,7,2,2,2,2,2,1] [8,6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg42 sg8314

lemma sg13319 : RowSquare [8,7,2,2,2,2,2,1] [8,6,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg42 sg8315

lemma sg13320 : RowSquare [8,7,2,2,2,2,2,1] [8,6,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg5934

lemma sg13321 : RowSquare [8,7,2,2,2,2,2,1] [8,6,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5945

lemma sg13322 : RowSquare [8,7,2,2,2,2,2,1] [8,6,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8330

lemma sg13323 : RowSquare [8,7,2,2,2,2,2,1] [8,6,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1149 sg3287

lemma sg13324 : RowSquare [8,7,2,2,2,2,2,1] [8,6,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1637 sg2555

lemma sg13325 : RowSquare [8,7,2,2,2,2,2,1] [8,6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg5936

lemma sg13326 : RowSquare [8,7,2,2,2,2,2,1] [8,6,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1593 sg2593

lemma sg13327 : RowSquare [8,7,2,2,2,2,2,1] [8,6,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1637 sg2556

lemma sg13328 : RowSquare [8,7,2,2,2,2,2,1] [8,6,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg5935

lemma sg13329 : RowSquare [8,7,2,2,2,2,2,1] [8,6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg365 sg5111

lemma sg13330 : RowSquare [8,7,2,2,2,2,2,1] [8,6,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1594 sg2593

lemma sg13331 : RowSquare [8,7,2,2,2,2,2,1] [8,6,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1595 sg2592

lemma sg13332 : RowSquare [8,7,2,2,2,2,2,1] [8,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg5937

lemma sg13333 : RowSquare [8,7,2,2,2,2,2,1] [8,6,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1596 sg2592

lemma sg13334 : RowSquare [8,7,2,2,2,2,2,1] [8,6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1597 sg2592

lemma sg13335 : RowSquare [8,7,2,2,2,2,2,1] [8,7,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10066

lemma sg13336 : RowSquare [8,7,2,2,2,2,2,1] [8,7,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg5934

lemma sg13337 : RowSquare [8,7,2,2,2,2,2,1] [8,7,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10078

lemma sg13338 : RowSquare [8,7,2,2,2,2,2,1] [8,7,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg10068

lemma sg13339 : RowSquare [8,7,2,2,2,2,2,1] [8,7,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1151 sg3287

end UniversalTensorSquare
end
end

end OAI
