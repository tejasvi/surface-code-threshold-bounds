import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7676 = true := by
  decide +kernel

theorem tot7676 : totK PD2M8K2 D2M8K2.t7676 = [0, 0, 0, 193747390187, 468398016633, 185520982336, 9658607886, 0] := by
  decide +kernel

theorem rows7677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7677 = true := by
  decide +kernel

theorem tot7677 : totK PD2M8K2 D2M8K2.t7677 = [0, 0, 0, 206561862624, 496409910545, 152198003906, 4922956474, 0] := by
  decide +kernel

theorem rows7678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7678 = true := by
  decide +kernel

theorem tot7678 : totK PD2M8K2 D2M8K2.t7678 = [0, 0, 0, 235125270368, 489205429990, 168115935260, 5274443905, 0] := by
  decide +kernel

theorem rows7679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7679 = true := by
  decide +kernel

theorem tot7679 : totK PD2M8K2 D2M8K2.t7679 = [0, 0, 94308027437, 323465554740, 378260597484, 121609692512, 8859721110, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
