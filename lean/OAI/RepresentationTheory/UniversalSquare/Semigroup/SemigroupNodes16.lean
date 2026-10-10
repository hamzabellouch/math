import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes13
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes11

namespace OAI

/-! Semigroup Nodes 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6934 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1005

lemma sg6935 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1003 sg1000

lemma sg6936 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1003 sg1001

lemma sg6937 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1004

lemma sg6938 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1005

lemma sg6939 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg1004

lemma sg6940 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1004 sg1001

lemma sg6941 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1005

lemma sg6942 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1001 sg1005

lemma sg6943 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1006

lemma sg6944 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1007

lemma sg6945 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1006

lemma sg6946 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1008

lemma sg6947 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg1006

lemma sg6948 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1006 sg1001

lemma sg6949 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1007

lemma sg6950 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1008

lemma sg6951 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1007

lemma sg6952 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg1001 sg1007

lemma sg6953 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1008

lemma sg6954 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg1001 sg1008

lemma sg6955 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1009

lemma sg6956 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1002 sg1002

lemma sg6957 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1010

lemma sg6958 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1009

lemma sg6959 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1011

lemma sg6960 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg1004

lemma sg6961 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg1009

lemma sg6962 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1012

lemma sg6963 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg1005

lemma sg6964 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1009 sg1001

lemma sg6965 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1013

lemma sg6966 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1010

lemma sg6967 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1003 sg1003

lemma sg6968 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1014

lemma sg6969 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1011

lemma sg6970 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1010

lemma sg6971 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1012

lemma sg6972 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1003 sg1005

lemma sg6973 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1010 sg1001

lemma sg6974 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1011

lemma sg6975 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1004 sg1004

lemma sg6976 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1012

lemma sg6977 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1011

lemma sg6978 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,3] := by
  exact rowSquare_join (by decide) sg1001 sg1011

lemma sg6979 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1012

lemma sg6980 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,2] := by
  exact rowSquare_join (by decide) sg1001 sg1012

lemma sg6981 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1015

lemma sg6982 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1013

lemma sg6983 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1003 sg1006

lemma sg6984 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1016

lemma sg6985 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1014

lemma sg6986 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1004 sg1006

lemma sg6987 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1003 sg1008

lemma sg6988 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,5,3,3,3] := by
  exact rowSquare_join (by decide) sg1001 sg1013

lemma sg6989 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1014

lemma sg6990 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1004 sg1007

lemma sg6991 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1014

lemma sg6992 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,5,4,3,2] := by
  exact rowSquare_join (by decide) sg1001 sg1014

lemma sg6993 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,5,4,4,1] := by
  exact rowSquare_join (by decide) sg1005 sg1008

lemma sg6994 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1015

lemma sg6995 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1006 sg1006

lemma sg6996 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1016

lemma sg6997 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1015

lemma sg6998 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1006 sg1007

lemma sg6999 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1015

lemma sg7000 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,6,3,3,2] := by
  exact rowSquare_join (by decide) sg1001 sg1015

lemma sg7001 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1016

lemma sg7002 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,6,4,3,1] := by
  exact rowSquare_join (by decide) sg1007 sg1008

lemma sg7003 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,6,4,4] := by
  exact rowSquare_join (by decide) sg1008 sg1008

lemma sg7004 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg1012

lemma sg7005 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1017 sg1001

lemma sg7006 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [7,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1019

lemma sg7007 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [7,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1004 sg1010

lemma sg7008 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [7,4,3,3,3] := by
  exact rowSquare_join (by decide) sg1001 sg1018

lemma sg7009 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [7,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1004 sg1011

lemma sg7010 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [7,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1020

lemma sg7011 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [7,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1021

lemma sg7012 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [7,5,4,2,2] := by
  exact rowSquare_join (by decide) sg1001 sg1021

lemma sg7013 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [7,6,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1022

lemma sg7014 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,1] := by
  exact rowSquare_join (by decide) sg1005 sg1015

lemma sg7015 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [7,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1004 sg1016

lemma sg7016 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [7,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1023

lemma sg7017 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [7,7,2,2,2] := by
  exact rowSquare_join (by decide) sg1001 sg1023

lemma sg7018 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [8,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg1019

lemma sg7019 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [8,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1004 sg1017

lemma sg7020 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1001 sg1024

lemma sg7021 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [8,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1028

lemma sg7022 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [9,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1029

lemma sg7023 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [9,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg1026

lemma sg7024 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [9,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1030

lemma sg7025 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg910 sg997

lemma sg7026 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1000

lemma sg7027 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1001

lemma sg7028 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1002

lemma sg7029 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg997 sg911

lemma sg7030 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg912

lemma sg7031 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1004

lemma sg7032 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg913

lemma sg7033 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1005

lemma sg7034 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg914

lemma sg7035 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg915

lemma sg7036 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg912

lemma sg7037 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1378

lemma sg7038 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg913

lemma sg7039 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1379

lemma sg7040 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg914

lemma sg7041 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg999 sg915

lemma sg7042 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg914

lemma sg7043 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1000 sg915

lemma sg7044 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1001 sg915

lemma sg7045 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1009

lemma sg7046 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg916

lemma sg7047 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1010

lemma sg7048 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg917

lemma sg7049 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg916

lemma sg7050 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1011

lemma sg7051 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg918

lemma sg7052 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1002 sg913

lemma sg7053 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1012

lemma sg7054 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg919

lemma sg7055 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg914

lemma sg7056 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg915

lemma sg7057 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1013

lemma sg7058 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg920

lemma sg7059 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg917

lemma sg7060 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1014

lemma sg7061 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg921

lemma sg7062 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg918

lemma sg7063 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg917

lemma sg7064 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg922

lemma sg7065 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg919

lemma sg7066 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1003 sg914

lemma sg7067 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1003 sg915

lemma sg7068 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg923

lemma sg7069 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1378

lemma sg7070 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg918

lemma sg7071 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1379

lemma sg7072 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg999 sg919

lemma sg7073 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg918

lemma sg7074 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1004 sg915

lemma sg7075 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg919

lemma sg7076 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1001 sg919

lemma sg7077 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1015

lemma sg7078 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg920

lemma sg7079 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1016

lemma sg7080 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1388

lemma sg7081 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg921

lemma sg7082 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg920

lemma sg7083 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg922

lemma sg7084 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg920

lemma sg7085 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1006 sg915

lemma sg7086 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1389

lemma sg7087 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg923

lemma sg7088 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg999 sg921

lemma sg7089 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg589 sg1377

lemma sg7090 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg922

lemma sg7091 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg921

lemma sg7092 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg1001 sg921

lemma sg7093 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg922

lemma sg7094 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg1001 sg922

lemma sg7095 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg923

lemma sg7096 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg589 sg1378

lemma sg7097 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg923

lemma sg7098 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,5,3,2] := by
  exact rowSquare_join (by decide) sg1001 sg923

lemma sg7099 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg590 sg1379

lemma sg7100 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1017

lemma sg7101 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg924

lemma sg7102 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1002 sg916

lemma sg7103 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1018

lemma sg7104 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg925

lemma sg7105 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg924

lemma sg7106 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1019

lemma sg7107 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg926

lemma sg7108 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg918

lemma sg7109 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg5197

lemma sg7110 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg927

lemma sg7111 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg919

lemma sg7112 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg5198

lemma sg7113 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5199

lemma sg7114 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1020

lemma sg7115 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg928

lemma sg7116 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg925

lemma sg7117 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg5200

lemma sg7118 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1021

lemma sg7119 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg929

lemma sg7120 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg926

lemma sg7121 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg5201

lemma sg7122 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg927

lemma sg7123 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1003 sg919

lemma sg7124 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg5202

lemma sg7125 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg5203

lemma sg7126 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg930

lemma sg7127 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg923

lemma sg7128 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5204

lemma sg7129 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1004 sg918

lemma sg7130 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5205

lemma sg7131 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg5206

lemma sg7132 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,4,3,3] := by
  exact rowSquare_join (by decide) sg1 sg5207

lemma sg7133 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5208

lemma sg7134 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,4,4,4,2] := by
  exact rowSquare_join (by decide) sg1 sg5209

lemma sg7135 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1022

lemma sg7136 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg931

lemma sg7137 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg928

lemma sg7138 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1003 sg920

lemma sg7139 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg932

lemma sg7140 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg929

lemma sg7141 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg999 sg928

lemma sg7142 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1004 sg920

lemma sg7143 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1003 sg922

lemma sg7144 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg928

lemma sg7145 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,3,3,3] := by
  exact rowSquare_join (by decide) sg1001 sg928

lemma sg7146 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg930

lemma sg7147 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg929

lemma sg7148 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1004 sg921

lemma sg7149 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg929

lemma sg7150 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,4,3,2] := by
  exact rowSquare_join (by decide) sg1001 sg929

lemma sg7151 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,4,4,1] := by
  exact rowSquare_join (by decide) sg1005 sg922

lemma sg7152 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg930

lemma sg7153 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg930

lemma sg7154 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,5,2,2] := by
  exact rowSquare_join (by decide) sg1001 sg930

lemma sg7155 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,5,3,1] := by
  exact rowSquare_join (by decide) sg1005 sg923

lemma sg7156 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,5,5,4] := by
  exact rowSquare_join (by decide) sg594 sg1379

lemma sg7157 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1023

lemma sg7158 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1399

lemma sg7159 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg931

lemma sg7160 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1006 sg920

lemma sg7161 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg932

lemma sg7162 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg931

lemma sg7163 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1006 sg921

lemma sg7164 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg931

lemma sg7165 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,3,3,2] := by
  exact rowSquare_join (by decide) sg1001 sg931

lemma sg7166 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg932

lemma sg7167 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg932

lemma sg7168 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,4,2,2] := by
  exact rowSquare_join (by decide) sg1001 sg932

lemma sg7169 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,4,3,1] := by
  exact rowSquare_join (by decide) sg1007 sg922

lemma sg7170 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,4,4] := by
  exact rowSquare_join (by decide) sg1008 sg922

lemma sg7171 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg589 sg1389

lemma sg7172 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,5,2,1] := by
  exact rowSquare_join (by decide) sg1007 sg923

lemma sg7173 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,5,3] := by
  exact rowSquare_join (by decide) sg1008 sg923

lemma sg7174 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1024

lemma sg7175 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg933

lemma sg7176 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg5210

lemma sg7177 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1025

lemma sg7178 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg934

lemma sg7179 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5211

lemma sg7180 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg5212

lemma sg7181 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1026

lemma sg7182 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg935

lemma sg7183 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5213

lemma sg7184 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg5214

lemma sg7185 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5215

lemma sg7186 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5216

lemma sg7187 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg5217

lemma sg7188 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg5218

lemma sg7189 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1027

lemma sg7190 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg936

lemma sg7191 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg934

lemma sg7192 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg5219

lemma sg7193 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg937

lemma sg7194 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg935

lemma sg7195 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5220

lemma sg7196 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg5221

lemma sg7197 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5222

lemma sg7198 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg5223

lemma sg7199 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,4,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg5224

lemma sg7200 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg930

lemma sg7201 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5225

lemma sg7202 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg5226

lemma sg7203 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5227

lemma sg7204 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,4,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg3757

lemma sg7205 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,4,4,4,1] := by
  exact rowSquare_join (by decide) sg13 sg3758

lemma sg7206 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1028

lemma sg7207 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg938

lemma sg7208 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg936

lemma sg7209 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5228

lemma sg7210 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg5229

lemma sg7211 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg937

lemma sg7212 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5230

lemma sg7213 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg5231

lemma sg7214 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5232

lemma sg7215 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg3759

lemma sg7216 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5233

lemma sg7217 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5234

lemma sg7218 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,4,2,2] := by
  exact rowSquare_join (by decide) sg1 sg5235

lemma sg7219 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg3760

lemma sg7220 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,4,4] := by
  exact rowSquare_join (by decide) sg13 sg3761

lemma sg7221 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg1004 sg930

lemma sg7222 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,5,2,1] := by
  exact rowSquare_join (by decide) sg13 sg3762

lemma sg7223 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,5,3] := by
  exact rowSquare_join (by decide) sg13 sg3763

lemma sg7224 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg939

lemma sg7225 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg938

lemma sg7226 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1003 sg931

lemma sg7227 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1006 sg928

lemma sg7228 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg938

lemma sg7229 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,6,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg938

lemma sg7230 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,6,3,2,2] := by
  exact rowSquare_join (by decide) sg1001 sg938

lemma sg7231 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1004 sg932

lemma sg7232 : RowSquare [5,5,2,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg910 sg910

lemma sg7233 : RowSquare [5,5,2,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg910 sg911

lemma sg7234 : RowSquare [5,5,2,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg910 sg912

lemma sg7235 : RowSquare [5,5,2,2,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg915

lemma sg7236 : RowSquare [5,5,2,2,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg910 sg916

lemma sg7237 : RowSquare [5,5,2,2,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg911 sg911

lemma sg7238 : RowSquare [5,5,2,2,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg838

lemma sg7239 : RowSquare [5,5,2,2,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg920

lemma sg7240 : RowSquare [5,5,2,2,1,1,1,1,1,1] [4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg838

lemma sg7241 : RowSquare [5,5,2,2,1,1,1,1,1,1] [4,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg921

lemma sg7242 : RowSquare [5,5,2,2,1,1,1,1,1,1] [4,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg922

lemma sg7243 : RowSquare [5,5,2,2,1,1,1,1,1,1] [4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg840

lemma sg7244 : RowSquare [5,5,2,2,1,1,1,1,1,1] [4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg841

lemma sg7245 : RowSquare [5,5,2,2,1,1,1,1,1,1] [4,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg923

lemma sg7246 : RowSquare [5,5,2,2,1,1,1,1,1,1] [4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg840

lemma sg7247 : RowSquare [5,5,2,2,1,1,1,1,1,1] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1001 sg841

lemma sg7248 : RowSquare [5,5,2,2,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg842

lemma sg7249 : RowSquare [5,5,2,2,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg931

lemma sg7250 : RowSquare [5,5,2,2,1,1,1,1,1,1] [5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg846

lemma sg7251 : RowSquare [5,5,2,2,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg932

lemma sg7252 : RowSquare [5,5,2,2,1,1,1,1,1,1] [5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1006 sg841

lemma sg7253 : RowSquare [5,5,2,2,1,1,1,1,1,1] [5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg536 sg1377

lemma sg7254 : RowSquare [5,5,2,2,1,1,1,1,1,1] [5,5,5,5] := by
  exact rowSquare_join (by decide) sg13 sg3768

lemma sg7255 : RowSquare [5,5,2,2,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg939

lemma sg7256 : RowSquare [5,5,2,2,2,2,1,1] [4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg3998

lemma sg7257 : RowSquare [5,5,2,2,2,2,1,1] [4,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg3999

lemma sg7258 : RowSquare [5,5,2,2,2,2,1,1] [4,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg3999

lemma sg7259 : RowSquare [5,5,2,2,2,2,1,1] [4,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg4001

lemma sg7260 : RowSquare [5,5,2,2,2,2,1,1] [4,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg4002

lemma sg7261 : RowSquare [5,5,2,2,2,2,1,1] [4,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg4003

lemma sg7262 : RowSquare [5,5,2,2,2,2,1,1] [4,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg16 sg4004

lemma sg7263 : RowSquare [5,5,2,2,2,2,1,1] [4,4,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg4000

lemma sg7264 : RowSquare [5,5,2,2,2,2,1,1] [4,4,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg4001

lemma sg7265 : RowSquare [5,5,2,2,2,2,1,1] [4,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg4002

lemma sg7266 : RowSquare [5,5,2,2,2,2,1,1] [4,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg4003

lemma sg7267 : RowSquare [5,5,2,2,2,2,1,1] [4,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg4004

lemma sg7268 : RowSquare [5,5,2,2,2,2,1,1] [4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg838 sg838

lemma sg7269 : RowSquare [5,5,2,2,2,2,1,1] [5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg3998

lemma sg7270 : RowSquare [5,5,2,2,2,2,1,1] [5,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg3999

lemma sg7271 : RowSquare [5,5,2,2,2,2,1,1] [5,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg4002

lemma sg7272 : RowSquare [5,5,2,2,2,2,1,1] [5,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg4003

lemma sg7273 : RowSquare [5,5,2,2,2,2,1,1] [5,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18 sg4004

lemma sg7274 : RowSquare [5,5,2,2,2,2,1,1] [5,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg4009

lemma sg7275 : RowSquare [5,5,2,2,2,2,1,1] [5,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg4007

lemma sg7276 : RowSquare [5,5,2,2,2,2,1,1] [5,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg4009

lemma sg7277 : RowSquare [5,5,2,2,2,2,1,1] [5,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg4012

lemma sg7278 : RowSquare [5,5,2,2,2,2,1,1] [5,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg4013

lemma sg7279 : RowSquare [5,5,2,2,2,2,1,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg3999

lemma sg7280 : RowSquare [5,5,2,2,2,2,1,1] [6,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg4002

lemma sg7281 : RowSquare [5,5,2,2,2,2,1,1] [6,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg4003

lemma sg7282 : RowSquare [5,5,2,2,2,2,1,1] [6,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19 sg4004

lemma sg7283 : RowSquare [5,5,2,2,2,2,1,1] [6,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg4009

lemma sg7284 : RowSquare [5,5,2,2,2,2,1,1] [6,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg4021

lemma sg7285 : RowSquare [5,5,2,2,2,2,1,1] [7,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg4009

lemma sg7286 : RowSquare [5,5,3,2,1,1,1,1,1] [4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg313 sg1688

lemma sg7287 : RowSquare [5,5,3,2,1,1,1,1,1] [5,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg316 sg1688

lemma sg7288 : RowSquare [5,5,3,2,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg324 sg1682

lemma sg7289 : RowSquare [5,5,3,2,1,1,1,1,1] [7,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg325 sg1683

lemma sg7290 : RowSquare [5,5,3,2,1,1,1,1,1] [7,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg326 sg1683

lemma sg7291 : RowSquare [5,5,3,2,1,1,1,1,1] [7,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg327 sg1683

lemma sg7292 : RowSquare [6,4,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg682 sg1327

lemma sg7293 : RowSquare [6,4,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg677 sg1328

lemma sg7294 : RowSquare [6,4,1,1,1,1,1,1,1,1,1,1] [6,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg683 sg1327

lemma sg7295 : RowSquare [6,4,1,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg678 sg1328

lemma sg7296 : RowSquare [6,4,1,1,1,1,1,1,1,1,1,1] [6,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg684 sg1327

lemma sg7297 : RowSquare [6,4,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg679 sg1328

lemma sg7298 : RowSquare [6,4,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg677 sg1332

lemma sg7299 : RowSquare [6,4,1,1,1,1,1,1,1,1,1,1] [6,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg685 sg1327

lemma sg7300 : RowSquare [6,4,1,1,1,1,1,1,1,1,1,1] [6,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg680 sg1328

lemma sg7301 : RowSquare [6,4,1,1,1,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg681 sg1328

lemma sg7302 : RowSquare [6,4,1,1,1,1,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg686 sg1327

lemma sg7303 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1332

lemma sg7304 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg370 sg1758

lemma sg7305 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg372 sg1755

lemma sg7306 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg1755

lemma sg7307 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg889 sg1033

lemma sg7308 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg614 sg1332

lemma sg7309 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg372 sg1756

lemma sg7310 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1031 sg890

lemma sg7311 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg1756

lemma sg7312 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg892

lemma sg7313 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg615 sg1332

lemma sg7314 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg1757

lemma sg7315 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1033 sg892

lemma sg7316 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6081

lemma sg7317 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6082

lemma sg7318 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6083

lemma sg7319 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg617 sg1331

lemma sg7320 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6084

lemma sg7321 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg617 sg1332

lemma sg7322 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6085

lemma sg7323 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6086

lemma sg7324 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6087

lemma sg7325 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6088

lemma sg7326 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6089

lemma sg7327 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6090

lemma sg7328 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg618 sg1332

lemma sg7329 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg623 sg1328

lemma sg7330 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6091

lemma sg7331 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg619 sg1330

lemma sg7332 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6092

lemma sg7333 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg620 sg1330

end UniversalTensorSquare
end
end

end OAI
