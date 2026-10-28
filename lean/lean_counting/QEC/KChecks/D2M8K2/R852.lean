import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3408 = true := by
  decide +kernel

theorem tot3408 : totK PD2M8K2 D2M8K2.t3408 = [154546952829, 439624517572, 285017689966, 32430173922, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3409 = true := by
  decide +kernel

theorem tot3409 : totK PD2M8K2 D2M8K2.t3409 = [177086449974, 449715450588, 250545731977, 17095301934, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3410 = true := by
  decide +kernel

theorem tot3410 : totK PD2M8K2 D2M8K2.t3410 = [68371975852, 337878863584, 396432601987, 85311569289, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows3411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3411 = true := by
  decide +kernel

theorem tot3411 : totK PD2M8K2 D2M8K2.t3411 = [0, 209950139429, 487451567200, 171142511894, 9404247146, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
