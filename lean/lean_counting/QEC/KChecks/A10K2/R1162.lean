import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4648 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4648 = true := by
  decide +kernel

theorem tot4648 : totK PA10K2 A10K2.t4648 = [0, 0, 342275399197, 1448583826983, 2111877447918, 984208845598, 91805750933, 0, 0, 0] := by
  decide +kernel

theorem rows4649 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4649 = true := by
  decide +kernel

theorem tot4649 : totK PA10K2 A10K2.t4649 = [0, 0, 438682264787, 1733609643238, 2014911699717, 743293617700, 62702525251, 0, 0, 0] := by
  decide +kernel

theorem rows4650 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4650 = true := by
  decide +kernel

theorem tot4650 : totK PA10K2 A10K2.t4650 = [0, 0, 179423204105, 1080128090153, 2035221469020, 1354005156600, 214449877947, 6439430839, 0, 0] := by
  decide +kernel

theorem rows4651 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4651 = true := by
  decide +kernel

theorem tot4651 : totK PA10K2 A10K2.t4651 = [0, 0, 496921449435, 1856339595184, 2014328530622, 547961614679, 22108643497, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
