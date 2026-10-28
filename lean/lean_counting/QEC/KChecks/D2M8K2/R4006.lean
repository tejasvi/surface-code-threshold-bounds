import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16024 = true := by
  decide +kernel

theorem tot16024 : totK PD2M8K2 D2M8K2.t16024 = [0, 0, 0, 255042917645, 489403377754, 133024403783, 2464873236, 0] := by
  decide +kernel

theorem rows16025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16025 = true := by
  decide +kernel

theorem tot16025 : totK PD2M8K2 D2M8K2.t16025 = [0, 0, 0, 201088673200, 480195959419, 177212543852, 7760148276, 0] := by
  decide +kernel

theorem rows16026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16026 = true := by
  decide +kernel

theorem tot16026 : totK PD2M8K2 D2M8K2.t16026 = [0, 0, 0, 211337299442, 467901937518, 203496386651, 15786832490, 0] := by
  decide +kernel

theorem rows16027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16027 = true := by
  decide +kernel

theorem tot16027 : totK PD2M8K2 D2M8K2.t16027 = [0, 0, 99421869408, 322605553913, 334622888350, 131948223979, 9043051330, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
