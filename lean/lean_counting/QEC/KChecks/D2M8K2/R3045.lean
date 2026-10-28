import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12180 = true := by
  decide +kernel

theorem tot12180 : totK PD2M8K2 D2M8K2.t12180 = [87503642934, 300360006147, 371022865158, 119920573641, 5035903252, 0, 0, 0] := by
  decide +kernel

theorem rows12181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12181 = true := by
  decide +kernel

theorem tot12181 : totK PD2M8K2 D2M8K2.t12181 = [158741807936, 458610160481, 267598242882, 21225022324, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12182 = true := by
  decide +kernel

theorem tot12182 : totK PD2M8K2 D2M8K2.t12182 = [177877115015, 469322387374, 231633967198, 15843005254, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12183 = true := by
  decide +kernel

theorem tot12183 : totK PD2M8K2 D2M8K2.t12183 = [0, 290158550881, 512726997092, 96949234897, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
