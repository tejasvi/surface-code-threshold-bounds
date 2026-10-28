import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9472 = true := by
  decide +kernel

theorem tot9472 : totK PD2M8K2 D2M8K2.t9472 = [188996952905, 464476248245, 234760287412, 15929301168, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9473 = true := by
  decide +kernel

theorem tot9473 : totK PD2M8K2 D2M8K2.t9473 = [108414476679, 439219286235, 336270967979, 37912055310, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9474 = true := by
  decide +kernel

theorem tot9474 : totK PD2M8K2 D2M8K2.t9474 = [0, 171055939392, 443328054195, 258480147198, 25373788367, 0, 0, 0] := by
  decide +kernel

theorem rows9475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9475 = true := by
  decide +kernel

theorem tot9475 : totK PD2M8K2 D2M8K2.t9475 = [0, 183912999871, 508036697845, 208541484789, 5430665091, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
