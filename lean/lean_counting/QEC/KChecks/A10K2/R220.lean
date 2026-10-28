import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows880 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t880 = true := by
  decide +kernel

theorem tot880 : totK PA10K2 A10K2.t880 = [0, 563402293713, 1908111182142, 1754067607148, 461751661105, 30560571799, 0, 0, 0, 0] := by
  decide +kernel

theorem rows881 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t881 = true := by
  decide +kernel

theorem tot881 : totK PA10K2 A10K2.t881 = [420374455379, 1617742798583, 1921148389494, 770069762415, 71162070304, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows882 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t882 = true := by
  decide +kernel

theorem tot882 : totK PA10K2 A10K2.t882 = [309040822860, 1498438915154, 2170999694146, 903370520442, 77347551599, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows883 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t883 = true := by
  decide +kernel

theorem tot883 : totK PA10K2 A10K2.t883 = [109233960067, 647064986087, 1817251853237, 1795189843622, 438681756758, 24939049294, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
