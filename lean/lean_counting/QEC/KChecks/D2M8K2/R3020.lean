import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12080 = true := by
  decide +kernel

theorem tot12080 : totK PD2M8K2 D2M8K2.t12080 = [0, 142766348528, 355625127640, 304251476623, 99297062679, 3880716147, 0, 0] := by
  decide +kernel

theorem rows12081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12081 = true := by
  decide +kernel

theorem tot12081 : totK PD2M8K2 D2M8K2.t12081 = [0, 153636730739, 441474745885, 294803422381, 23957296264, 0, 0, 0] := by
  decide +kernel

theorem rows12082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12082 = true := by
  decide +kernel

theorem tot12082 : totK PD2M8K2 D2M8K2.t12082 = [0, 90526578066, 359142214501, 363915500715, 79897224556, 1231730743, 0, 0] := by
  decide +kernel

theorem rows12083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12083 = true := by
  decide +kernel

theorem tot12083 : totK PD2M8K2 D2M8K2.t12083 = [0, 0, 222031685509, 493543567648, 170892209751, 5003507424, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
