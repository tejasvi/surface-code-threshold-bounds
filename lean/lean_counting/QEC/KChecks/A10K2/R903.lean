import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3612 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3612 = true := by
  decide +kernel

theorem tot3612 : totK PA10K2 A10K2.t3612 = [0, 117664770764, 1075155727477, 2326804704654, 1493084621017, 185294921698, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3613 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3613 = true := by
  decide +kernel

theorem tot3613 : totK PA10K2 A10K2.t3613 = [0, 0, 505651702502, 1811581762114, 1996840389823, 688565573758, 48360659890, 0, 0, 0] := by
  decide +kernel

theorem rows3614 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3614 = true := by
  decide +kernel

theorem tot3614 : totK PA10K2 A10K2.t3614 = [0, 0, 463952771616, 1768013594924, 1986073760027, 541950840830, 32523532663, 0, 0, 0] := by
  decide +kernel

theorem rows3615 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3615 = true := by
  decide +kernel

theorem tot3615 : totK PA10K2 A10K2.t3615 = [0, 0, 180428436061, 1152535217015, 2079993596224, 1228823751991, 248708063226, 20331139758, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
