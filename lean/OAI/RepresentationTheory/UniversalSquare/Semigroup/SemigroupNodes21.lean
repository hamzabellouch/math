import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes18
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes19

namespace OAI

/-! Semigroup Nodes 21. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8938 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [7,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1517 sg1428

lemma sg8939 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [7,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1520 sg1428

lemma sg8940 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1552

lemma sg8941 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1553

lemma sg8942 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1499 sg1552

lemma sg8943 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1554

lemma sg8944 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1500 sg1552

lemma sg8945 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1555

lemma sg8946 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1552 sg1501

lemma sg8947 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1552 sg1502

lemma sg8948 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1500 sg1553

lemma sg8949 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1501 sg1553

lemma sg8950 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1553 sg1502

lemma sg8951 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1500 sg1554

lemma sg8952 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1500 sg1555

lemma sg8953 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1501 sg1554

lemma sg8954 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,3] := by
  exact rowSquare_join (by decide) sg1502 sg1554

lemma sg8955 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1501 sg1555

lemma sg8956 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,2] := by
  exact rowSquare_join (by decide) sg1502 sg1555

lemma sg8957 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1556

lemma sg8958 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1503 sg1552

lemma sg8959 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1557

lemma sg8960 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1499 sg1556

lemma sg8961 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1504 sg1552

lemma sg8962 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1558

lemma sg8963 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1503 sg1554

lemma sg8964 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1500 sg1556

lemma sg8965 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1503 sg1555

lemma sg8966 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1501 sg1556

lemma sg8967 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1556 sg1502

lemma sg8968 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1559

lemma sg8969 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1499 sg1557

lemma sg8970 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1504 sg1553

lemma sg8971 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1560

lemma sg8972 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1499 sg1558

lemma sg8973 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1500 sg1557

lemma sg8974 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1505 sg1553

lemma sg8975 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1504 sg1555

lemma sg8976 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,3,3,3] := by
  exact rowSquare_join (by decide) sg1502 sg1557

lemma sg8977 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1500 sg1558

lemma sg8978 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1505 sg1554

lemma sg8979 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1501 sg1558

lemma sg8980 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1507 sg1553

lemma sg8981 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1891

lemma sg8982 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg2310

lemma sg8983 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2311

lemma sg8984 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg2312

lemma sg8985 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg911 sg1891

lemma sg8986 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg587 sg2310

lemma sg8987 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2314

lemma sg8988 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg587 sg2311

lemma sg8989 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1894

lemma sg8990 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2316

lemma sg8991 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1895

lemma sg8992 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2317

lemma sg8993 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg912 sg1891

lemma sg8994 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg588 sg2311

lemma sg8995 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg941 sg1874

lemma sg8996 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg589 sg2310

lemma sg8997 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg913 sg1891

lemma sg8998 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg589 sg2311

lemma sg8999 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2319

lemma sg9000 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg2310

lemma sg9001 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg914 sg1891

lemma sg9002 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg915 sg1891

lemma sg9003 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1092 sg1682

lemma sg9004 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1288 sg1498

lemma sg9005 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1093 sg1682

lemma sg9006 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1094 sg1682

lemma sg9007 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1288 sg1500

lemma sg9008 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg1794

lemma sg9009 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1095 sg1682

lemma sg9010 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1795

lemma sg9011 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg587 sg2312

lemma sg9012 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1288 sg1502

lemma sg9013 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1796

lemma sg9014 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8116

lemma sg9015 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg587 sg2314

lemma sg9016 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg0 sg8117

lemma sg9017 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg1797

lemma sg9018 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1798

lemma sg9019 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg940 sg1876

lemma sg9020 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1799

lemma sg9021 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8118

lemma sg9022 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1800

lemma sg9023 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8119

lemma sg9024 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8120

lemma sg9025 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg0 sg8121

lemma sg9026 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1801

lemma sg9027 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8122

lemma sg9028 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1802

lemma sg9029 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg942 sg1876

lemma sg9030 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8123

lemma sg9031 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8124

lemma sg9032 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8125

lemma sg9033 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg589 sg2314

lemma sg9034 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2323

lemma sg9035 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8126

lemma sg9036 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8127

lemma sg9037 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8128

lemma sg9038 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1000 sg1796

lemma sg9039 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1001 sg1796

lemma sg9040 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1898

lemma sg9041 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2324

lemma sg9042 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg1797

lemma sg9043 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg948 sg1874

lemma sg9044 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg940 sg1877

lemma sg9045 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1899

lemma sg9046 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2325

lemma sg9047 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1799

lemma sg9048 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg2316

lemma sg9049 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1800

lemma sg9050 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg920 sg1891

lemma sg9051 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg371 sg2746

lemma sg9052 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg949 sg1874

lemma sg9053 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1878

lemma sg9054 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg941 sg1877

lemma sg9055 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg950 sg1874

lemma sg9056 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1879

lemma sg9057 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1799

lemma sg9058 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1800

lemma sg9059 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg615 sg2281

lemma sg9060 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg2921

lemma sg9061 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg922 sg1891

lemma sg9062 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg1799

lemma sg9063 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1000 sg1800

lemma sg9064 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg1001 sg1800

lemma sg9065 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1900

lemma sg9066 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg951 sg1874

lemma sg9067 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg2922

lemma sg9068 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg941 sg1878

lemma sg9069 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg2923

lemma sg9070 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg941 sg1879

lemma sg9071 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg942 sg1878

lemma sg9072 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg943 sg1878

lemma sg9073 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg3006

lemma sg9074 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg942 sg1879

lemma sg9075 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg943 sg1879

lemma sg9076 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg373 sg2748

lemma sg9077 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg616 sg2282

lemma sg9078 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1289 sg1498

lemma sg9079 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1289 sg1499

lemma sg9080 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg1500

lemma sg9081 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg944 sg1876

lemma sg9082 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg1501

lemma sg9083 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8129

lemma sg9084 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg1502

lemma sg9085 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8130

lemma sg9086 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8131

lemma sg9087 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg0 sg8132

lemma sg9088 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1372 sg1411

lemma sg9089 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1408 sg1373

lemma sg9090 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1292

lemma sg9091 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8133

lemma sg9092 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1372 sg1412

lemma sg9093 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8134

lemma sg9094 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8135

lemma sg9095 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8136

lemma sg9096 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8137

lemma sg9097 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg8138

lemma sg9098 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1293

lemma sg9099 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8139

lemma sg9100 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8140

lemma sg9101 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1294

lemma sg9102 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8141

lemma sg9103 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8142

lemma sg9104 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6556

lemma sg9105 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg0 sg8143

lemma sg9106 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8144

lemma sg9107 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6557

lemma sg9108 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8145

lemma sg9109 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1 sg6558

lemma sg9110 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1 sg6559

lemma sg9111 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1804

lemma sg9112 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8146

lemma sg9113 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1805

lemma sg9114 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8147

lemma sg9115 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8148

lemma sg9116 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1806

lemma sg9117 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8149

lemma sg9118 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8150

lemma sg9119 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8151

lemma sg9120 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg0 sg8152

lemma sg9121 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1807

lemma sg9122 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8153

lemma sg9123 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8154

lemma sg9124 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8155

lemma sg9125 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8156

lemma sg9126 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8157

lemma sg9127 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg0 sg8158

lemma sg9128 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8159

lemma sg9129 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8160

lemma sg9130 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg0 sg8161

lemma sg9131 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1808

lemma sg9132 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8162

lemma sg9133 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8163

lemma sg9134 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg946 sg1878

lemma sg9135 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8164

lemma sg9136 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8165

lemma sg9137 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg4 sg5794

lemma sg9138 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8166

lemma sg9139 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,5,4,2] := by
  exact rowSquare_join (by decide) sg4 sg5795

lemma sg9140 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,5,5,5,1] := by
  exact rowSquare_join (by decide) sg0 sg8167

lemma sg9141 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2328

lemma sg9142 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1883

lemma sg9143 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg614 sg2283

lemma sg9144 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg956 sg1874

lemma sg9145 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1884

lemma sg9146 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1411 sg1377

lemma sg9147 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1885

lemma sg9148 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg931 sg1891

lemma sg9149 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg1774

lemma sg9150 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1006 sg1800

lemma sg9151 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg957 sg1874

lemma sg9152 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1886

lemma sg9153 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1520 sg1271

lemma sg9154 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1808

lemma sg9155 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1 sg6560

lemma sg9156 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [8,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg234 sg3299

lemma sg9157 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg910 sg1874

lemma sg9158 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg2288

lemma sg9159 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1371 sg1371

lemma sg9160 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg911 sg1874

lemma sg9161 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg2290

lemma sg9162 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg2291

lemma sg9163 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1877

lemma sg9164 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg912 sg1874

lemma sg9165 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2293

lemma sg9166 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1878

lemma sg9167 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg913 sg1874

lemma sg9168 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1879

lemma sg9169 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg914 sg1874

lemma sg9170 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg915 sg1874

lemma sg9171 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2297

lemma sg9172 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1371 sg1372

lemma sg9173 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1373

lemma sg9174 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg911 sg1875

lemma sg9175 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg1776

lemma sg9176 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1375

lemma sg9177 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1777

lemma sg9178 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg587 sg2290

lemma sg9179 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1376

lemma sg9180 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1881

lemma sg9181 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg912 sg1875

lemma sg9182 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1377

lemma sg9183 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1778

lemma sg9184 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg1776

lemma sg9185 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1777

lemma sg9186 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1378

lemma sg9187 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1780

lemma sg9188 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1776

lemma sg9189 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1379

lemma sg9190 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1781

lemma sg9191 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1776

lemma sg9192 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg1777

lemma sg9193 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1776

lemma sg9194 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1782

lemma sg9195 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg2297

lemma sg9196 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1777

lemma sg9197 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1777

lemma sg9198 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1883

lemma sg9199 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2305

lemma sg9200 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1884

lemma sg9201 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg920 sg1874

lemma sg9202 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1778

lemma sg9203 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1885

lemma sg9204 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2307

lemma sg9205 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1779

lemma sg9206 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg2293

lemma sg9207 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1886

lemma sg9208 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg921 sg1874

lemma sg9209 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1780

lemma sg9210 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg1778

lemma sg9211 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg922 sg1874

lemma sg9212 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1781

lemma sg9213 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1779

lemma sg9214 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1778

lemma sg9215 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1782

lemma sg9216 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg588 sg2297

lemma sg9217 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg1779

lemma sg9218 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1001 sg1779

lemma sg9219 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg923 sg1874

lemma sg9220 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1780

lemma sg9221 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1781

lemma sg9222 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg1780

lemma sg9223 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg1001 sg1780

lemma sg9224 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1782

lemma sg9225 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1781

lemma sg9226 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg1001 sg1781

lemma sg9227 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1782

lemma sg9228 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1001 sg1782

lemma sg9229 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1380

lemma sg9230 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1372 sg1372

lemma sg9231 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1498 sg1274

lemma sg9232 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1382

lemma sg9233 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1275

lemma sg9234 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1002 sg1776

lemma sg9235 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1383

lemma sg9236 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1276

lemma sg9237 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1002 sg1777

lemma sg9238 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1277

lemma sg9239 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1384

lemma sg9240 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1499 sg1274

lemma sg9241 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1385

lemma sg9242 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1372 sg1377

lemma sg9243 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1386

lemma sg9244 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1784

lemma sg9245 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1499 sg1276

lemma sg9246 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1003 sg1777

lemma sg9247 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1499 sg1277

lemma sg9248 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1387

lemma sg9249 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1278

lemma sg9250 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg1780

lemma sg9251 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6563

lemma sg9252 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1279

lemma sg9253 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg1781

lemma sg9254 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6564

lemma sg9255 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6565

lemma sg9256 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg1782

lemma sg9257 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1005 sg1777

lemma sg9258 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6566

lemma sg9259 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1 sg6567

lemma sg9260 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1 sg6568

lemma sg9261 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1887

lemma sg9262 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1785

lemma sg9263 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1783

lemma sg9264 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1388

lemma sg9265 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1786

lemma sg9266 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1373 sg1377

lemma sg9267 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg1783

lemma sg9268 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1787

lemma sg9269 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1784

lemma sg9270 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1003 sg1779

lemma sg9271 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1783

lemma sg9272 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1389

lemma sg9273 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1788

lemma sg9274 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1499 sg1278

lemma sg9275 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1374 sg1377

lemma sg9276 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1499 sg1279

lemma sg9277 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1784

lemma sg9278 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1375 sg1377

lemma sg9279 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1377 sg1376

lemma sg9280 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1003 sg1782

lemma sg9281 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1784

lemma sg9282 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg1001 sg1784

lemma sg9283 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1789

lemma sg9284 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg923 sg1876

lemma sg9285 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1500 sg1278

lemma sg9286 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg1004 sg1780

lemma sg9287 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1500 sg1279

lemma sg9288 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg1501 sg1278

lemma sg9289 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg1502 sg1278

lemma sg9290 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg1501 sg1279

lemma sg9291 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,5,4,2] := by
  exact rowSquare_join (by decide) sg1502 sg1279

lemma sg9292 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,5,5,1] := by
  exact rowSquare_join (by decide) sg1005 sg1782

lemma sg9293 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1888

lemma sg9294 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2309

lemma sg9295 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1785

lemma sg9296 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg2305

lemma sg9297 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1889

lemma sg9298 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg931 sg1874

lemma sg9299 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1786

lemma sg9300 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1785

lemma sg9301 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1787

lemma sg9302 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg588 sg2307

lemma sg9303 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg1785

lemma sg9304 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1001 sg1785

lemma sg9305 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg932 sg1874

lemma sg9306 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1788

lemma sg9307 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1377 sg1377

lemma sg9308 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1786

lemma sg9309 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,4,3,3] := by
  exact rowSquare_join (by decide) sg1001 sg1786

lemma sg9310 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1787

lemma sg9311 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,4,4,2] := by
  exact rowSquare_join (by decide) sg1001 sg1787

lemma sg9312 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1789

lemma sg9313 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1788

lemma sg9314 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg1377 sg1378

lemma sg9315 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg1377 sg1379

lemma sg9316 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,5,3,2] := by
  exact rowSquare_join (by decide) sg1001 sg1788

lemma sg9317 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,5,4,1] := by
  exact rowSquare_join (by decide) sg1007 sg1782

lemma sg9318 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,5,5] := by
  exact rowSquare_join (by decide) sg1008 sg1782

lemma sg9319 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1789

lemma sg9320 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1789

lemma sg9321 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,6,2,2] := by
  exact rowSquare_join (by decide) sg1378 sg1378

lemma sg9322 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,6,3,1] := by
  exact rowSquare_join (by decide) sg1378 sg1379

lemma sg9323 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,6,4] := by
  exact rowSquare_join (by decide) sg1379 sg1379

lemma sg9324 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1498 sg1280

lemma sg9325 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1499 sg1280

lemma sg9326 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1392

lemma sg9327 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1393

lemma sg9328 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1281

lemma sg9329 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6570

lemma sg9330 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1394

lemma sg9331 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1395

lemma sg9332 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1282

lemma sg9333 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1283

lemma sg9334 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1499 sg1281

lemma sg9335 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1396

lemma sg9336 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1284

lemma sg9337 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6576

end UniversalTensorSquare
end
end

end OAI
