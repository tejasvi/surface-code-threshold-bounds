import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2564 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2564 = true := by
  decide +kernel

theorem tot2564 : totK PA10K2 A10K2.t2564 = [266424507814, 1124300357371, 1862242118229, 1250866213585, 235506096072, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2565 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2565 = true := by
  decide +kernel

theorem tot2565 : totK PA10K2 A10K2.t2565 = [0, 783729235047, 2236127680151, 1558411394284, 278799777680, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2566 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2566 = true := by
  decide +kernel

theorem tot2566 : totK PA10K2 A10K2.t2566 = [0, 464483548312, 1741840297886, 1924246681570, 516114242086, 31222411477, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2567 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2567 = true := by
  decide +kernel

theorem tot2567 : totK PA10K2 A10K2.t2567 = [0, 81494255296, 843872925360, 1991311201965, 1476785918937, 359204035189, 25239774317, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
