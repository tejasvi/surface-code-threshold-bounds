import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8716 = true := by
  decide +kernel

theorem tot8716 : totK PD2M8K2 D2M8K2.t8716 = [0, 154811365446, 432557877668, 270113062641, 48166351199, 2481160468, 0, 0] := by
  decide +kernel

theorem rows8717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8717 = true := by
  decide +kernel

theorem tot8717 : totK PD2M8K2 D2M8K2.t8717 = [0, 154886592368, 442131408719, 278292535399, 24811102945, 0, 0, 0] := by
  decide +kernel

theorem rows8718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8718 = true := by
  decide +kernel

theorem tot8718 : totK PD2M8K2 D2M8K2.t8718 = [0, 90332340817, 353095702845, 360196202273, 74049795145, 1096505104, 0, 0] := by
  decide +kernel

theorem rows8719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8719 = true := by
  decide +kernel

theorem tot8719 : totK PD2M8K2 D2M8K2.t8719 = [0, 0, 276171447853, 512519876185, 110580424733, 1069412848, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
