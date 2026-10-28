import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4004 = true := by
  decide +kernel

theorem tot4004 : totK PD2M8K2 D2M8K2.t4004 = [0, 0, 177335064236, 476743201091, 233903985838, 12604928384, 0, 0] := by
  decide +kernel

theorem rows4005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4005 = true := by
  decide +kernel

theorem tot4005 : totK PD2M8K2 D2M8K2.t4005 = [0, 0, 153300587422, 441248434431, 262457975140, 20010637705, 0, 0] := by
  decide +kernel

theorem rows4006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4006 = true := by
  decide +kernel

theorem tot4006 : totK PD2M8K2 D2M8K2.t4006 = [0, 0, 0, 226134552142, 459485219621, 129809938466, 4787054165, 0] := by
  decide +kernel

theorem rows4007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4007 = true := by
  decide +kernel

theorem tot4007 : totK PD2M8K2 D2M8K2.t4007 = [0, 0, 149609352928, 441853327648, 260735466409, 22412164664, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
