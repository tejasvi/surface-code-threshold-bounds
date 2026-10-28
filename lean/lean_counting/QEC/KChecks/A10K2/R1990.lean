import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7960 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7960 = true := by
  decide +kernel

theorem tot7960 : totK PA10K2 A10K2.t7960 = [0, 0, 317143673244, 1360339253363, 1980883677795, 1067262615308, 144183487267, 0, 0, 0] := by
  decide +kernel

theorem rows7961 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7961 = true := by
  decide +kernel

theorem tot7961 : totK PA10K2 A10K2.t7961 = [0, 0, 300367622004, 1377049925076, 2052523020339, 975466949567, 94379317331, 0, 0, 0] := by
  decide +kernel

theorem rows7962 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7962 = true := by
  decide +kernel

theorem tot7962 : totK PA10K2 A10K2.t7962 = [0, 0, 537154219116, 1880879240423, 2013513530084, 600128492626, 35844756517, 0, 0, 0] := by
  decide +kernel

theorem rows7963 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7963 = true := by
  decide +kernel

theorem tot7963 : totK PA10K2 A10K2.t7963 = [0, 0, 121146523123, 1112220806474, 2248869239244, 1462615889332, 246841182743, 6279851884, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
