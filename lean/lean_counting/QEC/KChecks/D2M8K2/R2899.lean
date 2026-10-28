import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11596 = true := by
  decide +kernel

theorem tot11596 : totK PD2M8K2 D2M8K2.t11596 = [186320076485, 473476533445, 222701320280, 12346377983, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11597 = true := by
  decide +kernel

theorem tot11597 : totK PD2M8K2 D2M8K2.t11597 = [4187750769, 303701379626, 484180276270, 102533008839, 1163840124, 0, 0, 0] := by
  decide +kernel

theorem rows11598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11598 = true := by
  decide +kernel

theorem tot11598 : totK PD2M8K2 D2M8K2.t11598 = [0, 199605287780, 469530832931, 188216760164, 11873025674, 0, 0, 0] := by
  decide +kernel

theorem rows11599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11599 = true := by
  decide +kernel

theorem tot11599 : totK PD2M8K2 D2M8K2.t11599 = [177968616047, 447537167335, 280995388013, 32374052485, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
