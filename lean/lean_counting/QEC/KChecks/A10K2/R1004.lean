import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4016 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4016 = true := by
  decide +kernel

theorem tot4016 : totK PA10K2 A10K2.t4016 = [0, 0, 433723349535, 1819029488953, 2172029498552, 640475250276, 24442238019, 0, 0, 0] := by
  decide +kernel

theorem rows4017 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4017 = true := by
  decide +kernel

theorem tot4017 : totK PA10K2 A10K2.t4017 = [0, 0, 524975479317, 1831253607055, 1819177008238, 566216795203, 58163641935, 0, 0, 0] := by
  decide +kernel

theorem rows4018 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4018 = true := by
  decide +kernel

theorem tot4018 : totK PA10K2 A10K2.t4018 = [0, 0, 296957029898, 1482711828581, 2196506694301, 894559763161, 67798867528, 0, 0, 0] := by
  decide +kernel

theorem rows4019 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4019 = true := by
  decide +kernel

theorem tot4019 : totK PA10K2 A10K2.t4019 = [0, 0, 0, 503578028918, 1843510196256, 1826403320181, 491042026242, 31082886609, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
