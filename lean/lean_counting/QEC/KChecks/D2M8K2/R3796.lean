import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15184 = true := by
  decide +kernel

theorem tot15184 : totK PD2M8K2 D2M8K2.t15184 = [0, 0, 99770430304, 437164767324, 308174188822, 23816347815, 0, 0] := by
  decide +kernel

theorem rows15185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15185 = true := by
  decide +kernel

theorem tot15185 : totK PD2M8K2 D2M8K2.t15185 = [0, 0, 197741172188, 473082132663, 216110223937, 12740968741, 0, 0] := by
  decide +kernel

theorem rows15186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15186 = true := by
  decide +kernel

theorem tot15186 : totK PD2M8K2 D2M8K2.t15186 = [0, 0, 185530817851, 472619808411, 209396968400, 8932258738, 0, 0] := by
  decide +kernel

theorem rows15187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15187 = true := by
  decide +kernel

theorem tot15187 : totK PD2M8K2 D2M8K2.t15187 = [0, 0, 177151829298, 473687613960, 236007277369, 12828557351, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
