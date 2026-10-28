import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8392 = true := by
  decide +kernel

theorem tot8392 : totK PD2M8K2 D2M8K2.t8392 = [0, 0, 198745167067, 462857888277, 170056674646, 11727338389, 0, 0] := by
  decide +kernel

theorem rows8393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8393 = true := by
  decide +kernel

theorem tot8393 : totK PD2M8K2 D2M8K2.t8393 = [0, 156163025802, 449725301668, 284378530724, 24931804660, 0, 0, 0] := by
  decide +kernel

theorem rows8394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8394 = true := by
  decide +kernel

theorem tot8394 : totK PD2M8K2 D2M8K2.t8394 = [0, 176036933877, 458953702023, 241510309618, 13963869868, 0, 0, 0] := by
  decide +kernel

theorem rows8395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8395 = true := by
  decide +kernel

theorem tot8395 : totK PD2M8K2 D2M8K2.t8395 = [0, 86407673651, 332615521427, 391511288409, 81145706035, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
