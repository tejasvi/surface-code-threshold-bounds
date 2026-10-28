import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14096 = true := by
  decide +kernel

theorem tot14096 : totK PD2M8K2 D2M8K2.t14096 = [0, 0, 253001341014, 508511852172, 132941415973, 2242111996, 0, 0] := by
  decide +kernel

theorem rows14097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14097 = true := by
  decide +kernel

theorem tot14097 : totK PD2M8K2 D2M8K2.t14097 = [0, 78493953735, 289610317914, 377585258111, 132277734407, 6826432136, 0, 0] := by
  decide +kernel

theorem rows14098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14098 = true := by
  decide +kernel

theorem tot14098 : totK PD2M8K2 D2M8K2.t14098 = [0, 180399678129, 455200237737, 258849090494, 24336378053, 0, 0, 0] := by
  decide +kernel

theorem rows14099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14099 = true := by
  decide +kernel

theorem tot14099 : totK PD2M8K2 D2M8K2.t14099 = [0, 156223653761, 470392031693, 264157654630, 16538320921, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
