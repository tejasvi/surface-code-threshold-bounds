import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15540 = true := by
  decide +kernel

theorem tot15540 : totK PD2M8K2 D2M8K2.t15540 = [0, 190007932928, 467309999784, 223292621385, 12346377983, 0, 0, 0] := by
  decide +kernel

theorem rows15541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15541 = true := by
  decide +kernel

theorem tot15541 : totK PD2M8K2 D2M8K2.t15541 = [0, 37752960748, 328371168558, 444403039709, 94712291664, 1163840124, 0, 0] := by
  decide +kernel

theorem rows15542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15542 = true := by
  decide +kernel

theorem tot15542 : totK PD2M8K2 D2M8K2.t15542 = [0, 0, 202409546326, 473016942762, 184692017469, 11873025674, 0, 0] := by
  decide +kernel

theorem rows15543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15543 = true := by
  decide +kernel

theorem tot15543 : totK PD2M8K2 D2M8K2.t15543 = [0, 177909920641, 434731580121, 287866242327, 39662804479, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
