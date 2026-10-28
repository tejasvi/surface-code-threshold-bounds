import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9480 = true := by
  decide +kernel

theorem tot9480 : totK PD2M8K2 D2M8K2.t9480 = [195291747717, 466281655672, 247406083727, 23379811609, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9481 = true := by
  decide +kernel

theorem tot9481 : totK PD2M8K2 D2M8K2.t9481 = [186167539691, 476771136057, 228699711956, 12435138033, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9482 = true := by
  decide +kernel

theorem tot9482 : totK PD2M8K2 D2M8K2.t9482 = [0, 293798853505, 504846509523, 112476096606, 1197396724, 0, 0, 0] := by
  decide +kernel

theorem rows9483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9483 = true := by
  decide +kernel

theorem tot9483 : totK PD2M8K2 D2M8K2.t9483 = [8186756758, 199226323519, 472162780056, 191878109825, 12006692157, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
