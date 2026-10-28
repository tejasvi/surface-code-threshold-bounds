import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8076 = true := by
  decide +kernel

theorem tot8076 : totK PD2M8K2 D2M8K2.t8076 = [0, 0, 196470813973, 485152519975, 207729605365, 7870241454, 0, 0] := by
  decide +kernel

theorem rows8077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8077 = true := by
  decide +kernel

theorem tot8077 : totK PD2M8K2 D2M8K2.t8077 = [0, 164044448628, 339573439086, 276314238502, 135102893707, 13468148062, 0, 0] := by
  decide +kernel

theorem rows8078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8078 = true := by
  decide +kernel

theorem tot8078 : totK PD2M8K2 D2M8K2.t8078 = [0, 185166647356, 464628486881, 234597397228, 15742502998, 0, 0, 0] := by
  decide +kernel

theorem rows8079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8079 = true := by
  decide +kernel

theorem tot8079 : totK PD2M8K2 D2M8K2.t8079 = [0, 89733435092, 427080709703, 360137450142, 44177663649, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
