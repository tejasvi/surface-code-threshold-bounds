import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9268 = true := by
  decide +kernel

theorem tot9268 : totK PD2M8K2 D2M8K2.t9268 = [0, 298659068774, 516197294647, 98210014254, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows9269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9269 = true := by
  decide +kernel

theorem tot9269 : totK PD2M8K2 D2M8K2.t9269 = [167254128862, 382301952366, 261778015053, 82512468047, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows9270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9270 = true := by
  decide +kernel

theorem tot9270 : totK PD2M8K2 D2M8K2.t9270 = [178471279803, 447837804687, 275203771230, 30205735094, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9271 = true := by
  decide +kernel

theorem tot9271 : totK PD2M8K2 D2M8K2.t9271 = [0, 294483882860, 496026552768, 107622763516, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
