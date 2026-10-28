import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5288 = true := by
  decide +kernel

theorem tot5288 : totK PD2M8K2 D2M8K2.t5288 = [0, 86488944823, 408338669796, 371357636945, 41267022396, 0, 0, 0] := by
  decide +kernel

theorem rows5289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5289 = true := by
  decide +kernel

theorem tot5289 : totK PD2M8K2 D2M8K2.t5289 = [0, 83483105254, 309307625373, 389801654843, 106068044205, 3884009855, 0, 0] := by
  decide +kernel

theorem rows5290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5290 = true := by
  decide +kernel

theorem tot5290 : totK PD2M8K2 D2M8K2.t5290 = [0, 177936335313, 463309419778, 256507566979, 23050312993, 0, 0, 0] := by
  decide +kernel

theorem rows5291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5291 = true := by
  decide +kernel

theorem tot5291 : totK PD2M8K2 D2M8K2.t5291 = [0, 164957808545, 465614386464, 266085070397, 16639755792, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
