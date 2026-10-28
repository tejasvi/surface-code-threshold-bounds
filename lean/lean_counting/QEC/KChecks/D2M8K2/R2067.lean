import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8268 = true := by
  decide +kernel

theorem tot8268 : totK PD2M8K2 D2M8K2.t8268 = [0, 86118695557, 352157282761, 357281510334, 66373920131, 1206465782, 0, 0] := by
  decide +kernel

theorem rows8269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8269 = true := by
  decide +kernel

theorem tot8269 : totK PD2M8K2 D2M8K2.t8269 = [0, 43540716579, 376745397966, 416752934176, 41715777069, 0, 0, 0] := by
  decide +kernel

theorem rows8270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8270 = true := by
  decide +kernel

theorem tot8270 : totK PD2M8K2 D2M8K2.t8270 = [0, 201267706909, 469376015692, 221760139263, 16104584588, 0, 0, 0] := by
  decide +kernel

theorem rows8271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8271 = true := by
  decide +kernel

theorem tot8271 : totK PD2M8K2 D2M8K2.t8271 = [0, 175677785966, 472585818041, 221601305778, 12183533023, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
