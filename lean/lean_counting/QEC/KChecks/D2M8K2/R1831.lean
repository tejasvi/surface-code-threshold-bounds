import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7324 = true := by
  decide +kernel

theorem tot7324 : totK PD2M8K2 D2M8K2.t7324 = [0, 0, 186481247231, 469175524994, 225744945732, 15542835060, 0, 0] := by
  decide +kernel

theorem rows7325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7325 = true := by
  decide +kernel

theorem tot7325 : totK PD2M8K2 D2M8K2.t7325 = [0, 0, 176579752163, 442484528478, 276941717985, 28496840222, 0, 0] := by
  decide +kernel

theorem rows7326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7326 = true := by
  decide +kernel

theorem tot7326 : totK PD2M8K2 D2M8K2.t7326 = [0, 0, 177099220112, 485505569789, 246059637616, 8977779328, 0, 0] := by
  decide +kernel

theorem rows7327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7327 = true := by
  decide +kernel

theorem tot7327 : totK PD2M8K2 D2M8K2.t7327 = [0, 0, 0, 242394200820, 451162693957, 195519102920, 21385604922, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
