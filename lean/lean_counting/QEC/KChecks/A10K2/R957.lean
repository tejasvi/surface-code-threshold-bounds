import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3828 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3828 = true := by
  decide +kernel

theorem tot3828 : totK PA10K2 A10K2.t3828 = [0, 0, 0, 445595601406, 1792477955920, 1990318438813, 537513458970, 32523532663, 0, 0] := by
  decide +kernel

theorem rows3829 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3829 = true := by
  decide +kernel

theorem tot3829 : totK PA10K2 A10K2.t3829 = [0, 0, 0, 96815963306, 985727195482, 2056270900532, 1263036171791, 288592108074, 25130442608, 0] := by
  decide +kernel

theorem rows3830 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3830 = true := by
  decide +kernel

theorem tot3830 : totK PA10K2 A10K2.t3830 = [0, 0, 0, 308283808399, 1276483208279, 1885219315785, 1047539628078, 168837510838, 5517381808, 0] := by
  decide +kernel

theorem rows3831 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3831 = true := by
  decide +kernel

theorem tot3831 : totK PA10K2 A10K2.t3831 = [0, 0, 0, 468759140341, 1859456401084, 1946081105774, 461001794853, 26521581199, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
