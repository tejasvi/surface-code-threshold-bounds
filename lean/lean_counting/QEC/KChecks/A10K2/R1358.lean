import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5432 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5432 = true := by
  decide +kernel

theorem tot5432 : totK PA10K2 A10K2.t5432 = [0, 0, 252574754276, 1056871301815, 1849335539463, 1283110136112, 219496607351, 6034215561, 0, 0] := by
  decide +kernel

theorem rows5433 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5433 = true := by
  decide +kernel

theorem tot5433 : totK PA10K2 A10K2.t5433 = [0, 0, 537395797609, 1916836241383, 1839410974044, 470908321150, 26521581199, 0, 0, 0] := by
  decide +kernel

theorem rows5434 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5434 = true := by
  decide +kernel

theorem tot5434 : totK PA10K2 A10K2.t5434 = [0, 0, 0, 906155493520, 2380819671971, 1247011012816, 106336843274, 0, 0, 0] := by
  decide +kernel

theorem rows5435 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5435 = true := by
  decide +kernel

theorem tot5435 : totK PA10K2 A10K2.t5435 = [0, 0, 0, 581022278812, 1936659442980, 1714516935658, 370064748885, 12477276923, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
