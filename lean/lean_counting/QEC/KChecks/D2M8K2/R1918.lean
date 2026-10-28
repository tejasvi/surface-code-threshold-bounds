import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7672 = true := by
  decide +kernel

theorem tot7672 : totK PD2M8K2 D2M8K2.t7672 = [0, 0, 0, 168152950518, 470684302382, 228202917810, 13153212913, 0] := by
  decide +kernel

theorem rows7673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7673 = true := by
  decide +kernel

theorem tot7673 : totK PD2M8K2 D2M8K2.t7673 = [0, 0, 0, 187671319936, 469351083428, 205607570970, 12174977592, 0] := by
  decide +kernel

theorem rows7674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7674 = true := by
  decide +kernel

theorem tot7674 : totK PD2M8K2 D2M8K2.t7674 = [0, 0, 0, 208022894749, 477405972821, 173363160271, 10088849077, 0] := by
  decide +kernel

theorem rows7675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7675 = true := by
  decide +kernel

theorem tot7675 : totK PD2M8K2 D2M8K2.t7675 = [0, 0, 0, 254983779215, 492926449751, 119242876678, 2447184110, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
