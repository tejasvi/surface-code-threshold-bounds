import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows28 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t28 = true := by
  decide +kernel

theorem tot28 : totK PD2M8K2 D2M8K2.t28 = [0, 193005999271, 476484325255, 213075163131, 12595094539, 0, 0, 0] := by
  decide +kernel

theorem rows29 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t29 = true := by
  decide +kernel

theorem tot29 : totK PD2M8K2 D2M8K2.t29 = [0, 152870186436, 472001254342, 240822686992, 11127237002, 0, 0, 0] := by
  decide +kernel

theorem rows30 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t30 = true := by
  decide +kernel

theorem tot30 : totK PD2M8K2 D2M8K2.t30 = [0, 191885857878, 469892495009, 211030358935, 12403393969, 0, 0, 0] := by
  decide +kernel

theorem rows31 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t31 = true := by
  decide +kernel

theorem tot31 : totK PD2M8K2 D2M8K2.t31 = [0, 205441546121, 480901906783, 206561291551, 8394630506, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
