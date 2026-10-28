import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10440 = true := by
  decide +kernel

theorem tot10440 : totK PD2M8K2 D2M8K2.t10440 = [0, 0, 0, 229011879416, 483187420794, 193650084566, 15007737670, 0] := by
  decide +kernel

theorem rows10441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10441 = true := by
  decide +kernel

theorem tot10441 : totK PD2M8K2 D2M8K2.t10441 = [0, 0, 0, 189556789497, 470552442143, 218720445172, 11589250143, 0] := by
  decide +kernel

theorem rows10442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10442 = true := by
  decide +kernel

theorem tot10442 : totK PD2M8K2 D2M8K2.t10442 = [0, 0, 0, 191618126229, 475264401523, 220200164181, 16277061306, 0] := by
  decide +kernel

theorem rows10443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10443 = true := by
  decide +kernel

theorem tot10443 : totK PD2M8K2 D2M8K2.t10443 = [0, 0, 0, 191671238030, 469714356895, 219613656677, 12439805748, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
