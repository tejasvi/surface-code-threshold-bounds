import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3328 = true := by
  decide +kernel

theorem tot3328 : totK PD2M8K2 D2M8K2.t3328 = [0, 0, 294927131995, 499479384312, 102772187197, 1198073392, 0, 0] := by
  decide +kernel

theorem rows3329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3329 = true := by
  decide +kernel

theorem tot3329 : totK PD2M8K2 D2M8K2.t3329 = [0, 0, 196765172243, 470955130557, 199216829448, 12052611869, 0, 0] := by
  decide +kernel

theorem rows3330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3330 = true := by
  decide +kernel

theorem tot3330 : totK PD2M8K2 D2M8K2.t3330 = [0, 169623700993, 440309336113, 257631494756, 28637763672, 0, 0, 0] := by
  decide +kernel

theorem rows3331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3331 = true := by
  decide +kernel

theorem tot3331 : totK PD2M8K2 D2M8K2.t3331 = [0, 172019199296, 450436270114, 253651784005, 18667602043, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
