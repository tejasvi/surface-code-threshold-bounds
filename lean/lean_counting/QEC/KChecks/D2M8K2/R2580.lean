import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10320 = true := by
  decide +kernel

theorem tot10320 : totK PD2M8K2 D2M8K2.t10320 = [0, 0, 197617519842, 458176259950, 194305512925, 12135264383, 0, 0] := by
  decide +kernel

theorem rows10321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10321 = true := by
  decide +kernel

theorem tot10321 : totK PD2M8K2 D2M8K2.t10321 = [0, 0, 103509034827, 410199366462, 296539587108, 41931331419, 1138244013, 0] := by
  decide +kernel

theorem rows10322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10322 = true := by
  decide +kernel

theorem tot10322 : totK PD2M8K2 D2M8K2.t10322 = [0, 0, 48978881926, 372016436946, 405475219701, 41708079313, 0, 0] := by
  decide +kernel

theorem rows10323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10323 = true := by
  decide +kernel

theorem tot10323 : totK PD2M8K2 D2M8K2.t10323 = [0, 0, 177922935381, 458554907642, 249318514254, 24079365413, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
