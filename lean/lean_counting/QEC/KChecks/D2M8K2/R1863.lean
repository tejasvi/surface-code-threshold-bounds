import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7452 = true := by
  decide +kernel

theorem tot7452 : totK PD2M8K2 D2M8K2.t7452 = [0, 177791839573, 481519918708, 239311825336, 11473445677, 0, 0, 0] := by
  decide +kernel

theorem rows7453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7453 = true := by
  decide +kernel

theorem tot7453 : totK PD2M8K2 D2M8K2.t7453 = [0, 0, 278903536901, 509694767812, 111638330055, 1198073392, 0, 0] := by
  decide +kernel

theorem rows7454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7454 = true := by
  decide +kernel

theorem tot7454 : totK PD2M8K2 D2M8K2.t7454 = [0, 82463106879, 269227523756, 372014736080, 158376554855, 8401861322, 0, 0] := by
  decide +kernel

theorem rows7455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7455 = true := by
  decide +kernel

theorem tot7455 : totK PD2M8K2 D2M8K2.t7455 = [0, 178111173333, 466929021830, 257032230480, 23134859598, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
