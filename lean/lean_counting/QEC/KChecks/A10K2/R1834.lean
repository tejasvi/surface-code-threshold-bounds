import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7336 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7336 = true := by
  decide +kernel

theorem tot7336 : totK PA10K2 A10K2.t7336 = [0, 0, 0, 319190160972, 1209726491569, 1765440060206, 1218350933612, 385608516076, 28503589898, 0] := by
  decide +kernel

theorem rows7337 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7337 = true := by
  decide +kernel

theorem tot7337 : totK PA10K2 A10K2.t7337 = [0, 0, 0, 543313026720, 1895928838641, 1904824613099, 476092567447, 13032772403, 0, 0] := by
  decide +kernel

theorem rows7338 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7338 = true := by
  decide +kernel

theorem tot7338 : totK PA10K2 A10K2.t7338 = [0, 0, 0, 0, 633437474108, 2012208217098, 1631283172079, 389254804375, 25371180993, 0] := by
  decide +kernel

theorem rows7339 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7339 = true := by
  decide +kernel

theorem tot7339 : totK PA10K2 A10K2.t7339 = [0, 0, 0, 292562553233, 1244852665743, 1894060254025, 1156605315793, 199723457118, 5460492893, 0] := by
  decide +kernel

end QECKChecks.A10K2
