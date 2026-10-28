import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t260 = true := by
  decide +kernel

theorem tot260 : totK PD2M8K2 D2M8K2.t260 = [0, 173456152437, 464278381979, 250637223470, 20298891456, 0, 0, 0] := by
  decide +kernel

theorem rows261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t261 = true := by
  decide +kernel

theorem tot261 : totK PD2M8K2 D2M8K2.t261 = [0, 179781826033, 455784952059, 246579327783, 18185084111, 0, 0, 0] := by
  decide +kernel

theorem rows262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t262 = true := by
  decide +kernel

theorem tot262 : totK PD2M8K2 D2M8K2.t262 = [0, 0, 314280108587, 494212839082, 88403320983, 1096505104, 0, 0] := by
  decide +kernel

theorem rows263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t263 = true := by
  decide +kernel

theorem tot263 : totK PD2M8K2 D2M8K2.t263 = [0, 79164310099, 302095013051, 399357060279, 111860123693, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
