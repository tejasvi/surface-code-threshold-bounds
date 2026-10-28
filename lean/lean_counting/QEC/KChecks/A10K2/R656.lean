import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2624 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2624 = true := by
  decide +kernel

theorem tot2624 : totK PA10K2 A10K2.t2624 = [0, 0, 618054692071, 1997043188097, 1744055347873, 376433669062, 11866545492, 0, 0, 0] := by
  decide +kernel

theorem rows2625 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2625 = true := by
  decide +kernel

theorem tot2625 : totK PA10K2 A10K2.t2625 = [0, 0, 443010074553, 1687641815355, 1789760278970, 548385780723, 50109395967, 0, 0, 0] := by
  decide +kernel

theorem rows2626 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2626 = true := by
  decide +kernel

theorem tot2626 : totK PA10K2 A10K2.t2626 = [0, 0, 207095805940, 1433442997400, 2133407105772, 763394199170, 58344830985, 0, 0, 0] := by
  decide +kernel

theorem rows2627 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2627 = true := by
  decide +kernel

theorem tot2627 : totK PA10K2 A10K2.t2627 = [0, 317769054122, 960629082214, 1083010525663, 1201456364948, 894940902850, 207269719194, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
