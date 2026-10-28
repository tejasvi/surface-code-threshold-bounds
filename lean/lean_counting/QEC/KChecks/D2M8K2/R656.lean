import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2624 = true := by
  decide +kernel

theorem tot2624 : totK PD2M8K2 D2M8K2.t2624 = [0, 38807510282, 217146103213, 445928785031, 197273409745, 8214505460, 0, 0] := by
  decide +kernel

theorem rows2625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2625 = true := by
  decide +kernel

theorem tot2625 : totK PD2M8K2 D2M8K2.t2625 = [0, 202802326401, 473346107123, 232623311662, 22055373437, 0, 0, 0] := by
  decide +kernel

theorem rows2626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2626 = true := by
  decide +kernel

theorem tot2626 : totK PD2M8K2 D2M8K2.t2626 = [0, 177379182490, 476353490861, 227257691979, 12305796314, 0, 0, 0] := by
  decide +kernel

theorem rows2627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2627 = true := by
  decide +kernel

theorem tot2627 : totK PD2M8K2 D2M8K2.t2627 = [0, 0, 300920133739, 507697363997, 94163460313, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
