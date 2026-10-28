import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11244 = true := by
  decide +kernel

theorem tot11244 : totK PD2M8K2 D2M8K2.t11244 = [0, 182347403528, 459009587090, 238778968516, 16778243875, 0, 0, 0] := by
  decide +kernel

theorem rows11245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11245 = true := by
  decide +kernel

theorem tot11245 : totK PD2M8K2 D2M8K2.t11245 = [0, 76705733594, 405535185123, 377463800509, 44021305918, 0, 0, 0] := by
  decide +kernel

theorem rows11246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11246 = true := by
  decide +kernel

theorem tot11246 : totK PD2M8K2 D2M8K2.t11246 = [0, 0, 212784589333, 491579739197, 163084345577, 5218872685, 0, 0] := by
  decide +kernel

theorem rows11247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11247 = true := by
  decide +kernel

theorem tot11247 : totK PD2M8K2 D2M8K2.t11247 = [0, 190283383896, 438945825791, 250658729291, 29805011278, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
