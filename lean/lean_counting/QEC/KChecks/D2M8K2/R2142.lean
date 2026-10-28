import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8568 = true := by
  decide +kernel

theorem tot8568 : totK PD2M8K2 D2M8K2.t8568 = [172950304722, 388416891362, 246587110039, 99682613371, 6799735859, 0, 0, 0] := by
  decide +kernel

theorem rows8569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8569 = true := by
  decide +kernel

theorem tot8569 : totK PD2M8K2 D2M8K2.t8569 = [168982117002, 439536973169, 286614361057, 30437197709, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8570 = true := by
  decide +kernel

theorem tot8570 : totK PD2M8K2 D2M8K2.t8570 = [96163275464, 419394764347, 350243913511, 35336903909, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8571 = true := by
  decide +kernel

theorem tot8571 : totK PD2M8K2 D2M8K2.t8571 = [0, 216996586256, 489527403690, 185000726491, 9668735432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
