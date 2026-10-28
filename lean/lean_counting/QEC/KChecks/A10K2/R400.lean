import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1600 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1600 = true := by
  decide +kernel

theorem tot1600 : totK PA10K2 A10K2.t1600 = [0, 0, 0, 615867614229, 2017954296650, 1652742118271, 393426028390, 25565504801, 0, 0] := by
  decide +kernel

theorem rows1601 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1601 = true := by
  decide +kernel

theorem tot1601 : totK PA10K2 A10K2.t1601 = [0, 0, 382666486117, 1430858115834, 1777738118130, 968753381748, 172842896810, 5517381808, 0, 0] := by
  decide +kernel

theorem rows1602 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1602 = true := by
  decide +kernel

theorem tot1602 : totK PA10K2 A10K2.t1602 = [0, 0, 363236782290, 1607348416840, 2044907384773, 654093377274, 38254334585, 0, 0, 0] := by
  decide +kernel

theorem rows1603 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1603 = true := by
  decide +kernel

theorem tot1603 : totK PA10K2 A10K2.t1603 = [0, 0, 113873986223, 815071441547, 2043464016750, 1377664956951, 207609599557, 6121173289, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
