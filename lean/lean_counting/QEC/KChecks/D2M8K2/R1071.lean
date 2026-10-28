import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4284 = true := by
  decide +kernel

theorem tot4284 : totK PD2M8K2 D2M8K2.t4284 = [0, 0, 0, 304519551044, 523289145513, 85416497150, 0, 0] := by
  decide +kernel

theorem rows4285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4285 = true := by
  decide +kernel

theorem tot4285 : totK PD2M8K2 D2M8K2.t4285 = [0, 0, 149384902058, 374319354422, 279810022278, 87703983721, 2586295899, 0] := by
  decide +kernel

theorem rows4286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4286 = true := by
  decide +kernel

theorem tot4286 : totK PD2M8K2 D2M8K2.t4286 = [0, 0, 173958364945, 448506809040, 268729314853, 27122857504, 0, 0] := by
  decide +kernel

theorem rows4287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4287 = true := by
  decide +kernel

theorem tot4287 : totK PD2M8K2 D2M8K2.t4287 = [0, 0, 92333346222, 382830707228, 374400071268, 51205185913, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
