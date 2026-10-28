import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3080 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3080 = true := by
  decide +kernel

theorem tot3080 : totK PA10K2 A10K2.t3080 = [0, 0, 470781096417, 1548298902424, 1639214794724, 929620982555, 322722338517, 31276155898, 0, 0] := by
  decide +kernel

theorem rows3081 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3081 = true := by
  decide +kernel

theorem tot3081 : totK PA10K2 A10K2.t3081 = [0, 0, 498018207965, 1879094552070, 2019715545419, 526548612970, 19138079192, 0, 0, 0] := by
  decide +kernel

theorem rows3082 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3082 = true := by
  decide +kernel

theorem tot3082 : totK PA10K2 A10K2.t3082 = [0, 0, 569306206854, 1820906778295, 1782351016036, 535618138374, 36819311980, 0, 0, 0] := by
  decide +kernel

theorem rows3083 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3083 = true := by
  decide +kernel

theorem tot3083 : totK PA10K2 A10K2.t3083 = [0, 0, 0, 1071569352382, 2449274052981, 1066890097475, 81424914102, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
