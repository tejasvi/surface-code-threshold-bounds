import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3264 = true := by
  decide +kernel

theorem tot3264 : totK PD2M8K2 D2M8K2.t3264 = [0, 188165040727, 464287846545, 244856113745, 20859769259, 0, 0, 0] := by
  decide +kernel

theorem rows3265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3265 = true := by
  decide +kernel

theorem tot3265 : totK PD2M8K2 D2M8K2.t3265 = [0, 159920535544, 476753446273, 248118986669, 13491800230, 0, 0, 0] := by
  decide +kernel

theorem rows3266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3266 = true := by
  decide +kernel

theorem tot3266 : totK PD2M8K2 D2M8K2.t3266 = [0, 0, 290133334266, 491765407156, 90324509683, 1107157161, 0, 0] := by
  decide +kernel

theorem rows3267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3267 = true := by
  decide +kernel

theorem tot3267 : totK PD2M8K2 D2M8K2.t3267 = [0, 84478000207, 341974764196, 342756957270, 89846538833, 3824247485, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
