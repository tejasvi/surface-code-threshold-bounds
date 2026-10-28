import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1272 = true := by
  decide +kernel

theorem tot1272 : totK PD2M8K2 D2M8K2.t1272 = [0, 0, 226643406605, 477140343059, 163748059675, 8416438934, 0, 0] := by
  decide +kernel

theorem rows1273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1273 = true := by
  decide +kernel

theorem tot1273 : totK PD2M8K2 D2M8K2.t1273 = [0, 114968444822, 355347999334, 311538721285, 77597086017, 3436822651, 0, 0] := by
  decide +kernel

theorem rows1274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1274 = true := by
  decide +kernel

theorem tot1274 : totK PD2M8K2 D2M8K2.t1274 = [0, 187286401309, 461082076492, 236358886563, 18252358503, 0, 0, 0] := by
  decide +kernel

theorem rows1275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1275 = true := by
  decide +kernel

theorem tot1275 : totK PD2M8K2 D2M8K2.t1275 = [0, 19036468141, 331194775625, 440387252079, 71003113629, 1021600638, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
