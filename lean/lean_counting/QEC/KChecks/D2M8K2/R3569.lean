import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14276 = true := by
  decide +kernel

theorem tot14276 : totK PD2M8K2 D2M8K2.t14276 = [0, 189775379914, 475753454239, 217152780905, 14707859566, 0, 0, 0] := by
  decide +kernel

theorem rows14277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14277 = true := by
  decide +kernel

theorem tot14277 : totK PD2M8K2 D2M8K2.t14277 = [0, 199971497902, 471227395346, 206970061308, 7984731767, 0, 0, 0] := by
  decide +kernel

theorem rows14278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14278 = true := by
  decide +kernel

theorem tot14278 : totK PD2M8K2 D2M8K2.t14278 = [0, 99077668199, 399470868627, 333469405200, 46954601074, 1310285577, 0, 0] := by
  decide +kernel

theorem rows14279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14279 = true := by
  decide +kernel

theorem tot14279 : totK PD2M8K2 D2M8K2.t14279 = [0, 0, 298939872737, 507038802233, 66846530215, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
