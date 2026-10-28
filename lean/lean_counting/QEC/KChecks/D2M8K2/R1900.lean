import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7600 = true := by
  decide +kernel

theorem tot7600 : totK PD2M8K2 D2M8K2.t7600 = [0, 0, 293113158319, 523156204429, 99677885754, 1096505104, 0, 0] := by
  decide +kernel

theorem rows7601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7601 = true := by
  decide +kernel

theorem tot7601 : totK PD2M8K2 D2M8K2.t7601 = [0, 0, 213993278079, 492040637493, 176932425502, 5253830308, 0, 0] := by
  decide +kernel

theorem rows7602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7602 = true := by
  decide +kernel

theorem tot7602 : totK PD2M8K2 D2M8K2.t7602 = [0, 0, 179030907850, 461103896710, 201515485150, 12103679732, 0, 0] := by
  decide +kernel

theorem rows7603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7603 = true := by
  decide +kernel

theorem tot7603 : totK PD2M8K2 D2M8K2.t7603 = [0, 0, 66703461662, 366223791416, 355494518806, 54632366048, 1138244013, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
