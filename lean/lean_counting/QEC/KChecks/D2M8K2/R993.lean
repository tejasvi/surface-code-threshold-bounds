import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3972 = true := by
  decide +kernel

theorem tot3972 : totK PD2M8K2 D2M8K2.t3972 = [0, 0, 0, 304959517174, 467125354225, 83893978175, 1135526696, 0] := by
  decide +kernel

theorem rows3973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3973 = true := by
  decide +kernel

theorem tot3973 : totK PD2M8K2 D2M8K2.t3973 = [0, 0, 74134837701, 342206549885, 344817406148, 90943108448, 4028038878, 0] := by
  decide +kernel

theorem rows3974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3974 = true := by
  decide +kernel

theorem tot3974 : totK PD2M8K2 D2M8K2.t3974 = [0, 0, 281833591218, 476973287641, 123634748084, 3836120568, 0, 0] := by
  decide +kernel

theorem rows3975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3975 = true := by
  decide +kernel

theorem tot3975 : totK PD2M8K2 D2M8K2.t3975 = [0, 0, 205312543950, 470722309265, 201886784916, 11428133182, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
