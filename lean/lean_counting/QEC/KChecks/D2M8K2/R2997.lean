import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11988 = true := by
  decide +kernel

theorem tot11988 : totK PD2M8K2 D2M8K2.t11988 = [181015165609, 479247100880, 241340069458, 13998332970, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11989 = true := by
  decide +kernel

theorem tot11989 : totK PD2M8K2 D2M8K2.t11989 = [0, 280117611878, 518821327431, 102609302216, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows11990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11990 = true := by
  decide +kernel

theorem tot11990 : totK PD2M8K2 D2M8K2.t11990 = [0, 232419838109, 497508412458, 163403678259, 5253830308, 0, 0, 0] := by
  decide +kernel

theorem rows11991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11991 = true := by
  decide +kernel

theorem tot11991 : totK PD2M8K2 D2M8K2.t11991 = [0, 167433245115, 452793736970, 229297453778, 16891742343, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
