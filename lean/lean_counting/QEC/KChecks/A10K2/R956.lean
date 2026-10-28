import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3824 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3824 = true := by
  decide +kernel

theorem tot3824 : totK PA10K2 A10K2.t3824 = [0, 0, 298064684126, 1561107067626, 2114419799057, 748770677515, 53383554103, 0, 0, 0] := by
  decide +kernel

theorem rows3825 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3825 = true := by
  decide +kernel

theorem tot3825 : totK PA10K2 A10K2.t3825 = [0, 0, 112562677656, 815477511657, 2059785466583, 1485136184492, 248638969737, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3826 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3826 = true := by
  decide +kernel

theorem tot3826 : totK PA10K2 A10K2.t3826 = [0, 0, 390160844362, 1754803735049, 2199309292430, 734165399023, 53679850055, 0, 0, 0] := by
  decide +kernel

theorem rows3827 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3827 = true := by
  decide +kernel

theorem tot3827 : totK PA10K2 A10K2.t3827 = [0, 0, 0, 617571135167, 2115411341983, 1926947752900, 401953379351, 12926121504, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
