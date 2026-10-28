import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14624 = true := by
  decide +kernel

theorem tot14624 : totK PD2M8K2 D2M8K2.t14624 = [0, 0, 202444364668, 478266010367, 183799472656, 8660478446, 0, 0] := by
  decide +kernel

theorem rows14625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14625 = true := by
  decide +kernel

theorem tot14625 : totK PD2M8K2 D2M8K2.t14625 = [0, 0, 173474877445, 470180987948, 204763364299, 10636061198, 0, 0] := by
  decide +kernel

theorem rows14626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14626 = true := by
  decide +kernel

theorem tot14626 : totK PD2M8K2 D2M8K2.t14626 = [0, 0, 270537534017, 493672708783, 134985456857, 3032978471, 0, 0] := by
  decide +kernel

theorem rows14627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14627 = true := by
  decide +kernel

theorem tot14627 : totK PD2M8K2 D2M8K2.t14627 = [0, 57100535768, 220456620386, 417738461352, 203118267670, 12810146349, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
