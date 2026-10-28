import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2364 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2364 = true := by
  decide +kernel

theorem tot2364 : totK PA10K2 A10K2.t2364 = [0, 0, 305832627950, 1509649709301, 2051658415975, 701676684673, 52519180279, 0, 0, 0] := by
  decide +kernel

theorem rows2365 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2365 = true := by
  decide +kernel

theorem tot2365 : totK PA10K2 A10K2.t2365 = [0, 0, 292640272425, 1206563787112, 1853072189143, 1103686155985, 219157925173, 6354482628, 0, 0] := by
  decide +kernel

theorem rows2366 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2366 = true := by
  decide +kernel

theorem tot2366 : totK PA10K2 A10K2.t2366 = [0, 0, 267736007412, 1492760115822, 2165720766655, 747066774232, 52197625758, 0, 0, 0] := by
  decide +kernel

theorem rows2367 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2367 = true := by
  decide +kernel

theorem tot2367 : totK PA10K2 A10K2.t2367 = [0, 0, 241745644269, 1138205962002, 1894579427136, 1127606821744, 186532124298, 5447185874, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
