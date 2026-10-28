import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3700 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3700 = true := by
  decide +kernel

theorem tot3700 : totK PA10K2 A10K2.t3700 = [0, 0, 96817103441, 841750860779, 1973116615191, 1500093727956, 357794696087, 25565504801, 0, 0] := by
  decide +kernel

theorem rows3701 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3701 = true := by
  decide +kernel

theorem tot3701 : totK PA10K2 A10K2.t3701 = [0, 0, 197145467821, 1107636121044, 1972788469690, 1229015878436, 209933035668, 5517381808, 0, 0] := by
  decide +kernel

theorem rows3702 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3702 = true := by
  decide +kernel

theorem tot3702 : totK PA10K2 A10K2.t3702 = [0, 0, 584263778251, 1869531384543, 1773480361348, 515131835159, 31936107789, 0, 0, 0] := by
  decide +kernel

theorem rows3703 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3703 = true := by
  decide +kernel

theorem tot3703 : totK PA10K2 A10K2.t3703 = [0, 0, 0, 1081202834165, 2445137750232, 1074495408507, 77355190755, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
