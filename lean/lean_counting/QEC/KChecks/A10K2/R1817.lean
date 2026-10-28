import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7268 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7268 = true := by
  decide +kernel

theorem tot7268 : totK PA10K2 A10K2.t7268 = [0, 0, 305030648051, 1058809743945, 1596884684943, 1450136757960, 554772910152, 50425690648, 0, 0] := by
  decide +kernel

theorem rows7269 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7269 = true := by
  decide +kernel

theorem tot7269 : totK PA10K2 A10K2.t7269 = [0, 0, 474298433131, 1906752210793, 2135882265810, 569615027905, 18926013064, 0, 0, 0] := by
  decide +kernel

theorem rows7270 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7270 = true := by
  decide +kernel

theorem tot7270 : totK PA10K2 A10K2.t7270 = [0, 0, 0, 552455694537, 2006524603703, 1951617772472, 410417614257, 13576218110, 0, 0] := by
  decide +kernel

theorem rows7271 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7271 = true := by
  decide +kernel

theorem tot7271 : totK PA10K2 A10K2.t7271 = [0, 0, 504782908657, 1840835809324, 2054898771886, 766004489890, 69313458134, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
