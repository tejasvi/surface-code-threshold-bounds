import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1136 = true := by
  decide +kernel

theorem tot1136 : totK PD2M8K2 D2M8K2.t1136 = [0, 0, 275613515633, 509759673431, 113286151985, 1178750802, 0, 0] := by
  decide +kernel

theorem rows1137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1137 = true := by
  decide +kernel

theorem tot1137 : totK PD2M8K2 D2M8K2.t1137 = [0, 18419911429, 198758371066, 455678744645, 191224607412, 11991925116, 0, 0] := by
  decide +kernel

theorem rows1138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1138 = true := by
  decide +kernel

theorem tot1138 : totK PD2M8K2 D2M8K2.t1138 = [0, 182484820875, 442454903290, 240231661967, 22423585448, 0, 0, 0] := by
  decide +kernel

theorem rows1139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1139 = true := by
  decide +kernel

theorem tot1139 : totK PD2M8K2 D2M8K2.t1139 = [0, 189387229989, 459907300810, 231899298154, 16988898864, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
