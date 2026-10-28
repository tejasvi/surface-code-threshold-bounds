import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9136 = true := by
  decide +kernel

theorem tot9136 : totK PD2M8K2 D2M8K2.t9136 = [0, 172129141465, 439366721070, 281582406540, 34443789873, 0, 0, 0] := by
  decide +kernel

theorem rows9137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9137 = true := by
  decide +kernel

theorem tot9137 : totK PD2M8K2 D2M8K2.t9137 = [0, 193968765291, 481663222274, 227297435842, 11252110036, 0, 0, 0] := by
  decide +kernel

theorem rows9138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9138 = true := by
  decide +kernel

theorem tot9138 : totK PD2M8K2 D2M8K2.t9138 = [0, 52618497867, 283656656551, 382228938558, 174206141303, 19374288140, 0, 0] := by
  decide +kernel

theorem rows9139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9139 = true := by
  decide +kernel

theorem tot9139 : totK PD2M8K2 D2M8K2.t9139 = [0, 0, 212654220156, 486622691855, 189585546005, 5352136967, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
