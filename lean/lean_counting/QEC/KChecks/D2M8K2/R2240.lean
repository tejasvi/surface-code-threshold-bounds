import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8960 = true := by
  decide +kernel

theorem tot8960 : totK PD2M8K2 D2M8K2.t8960 = [171137772206, 461984032161, 260094500518, 24077127074, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8961 = true := by
  decide +kernel

theorem tot8961 : totK PD2M8K2 D2M8K2.t8961 = [181015165609, 473431296911, 236404729587, 15843005254, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8962 = true := by
  decide +kernel

theorem tot8962 : totK PD2M8K2 D2M8K2.t8962 = [0, 282577725701, 509961420708, 101022293090, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows8963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8963 = true := by
  decide +kernel

theorem tot8963 : totK PD2M8K2 D2M8K2.t8963 = [0, 251091322238, 502440264128, 147383270082, 5253830308, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
