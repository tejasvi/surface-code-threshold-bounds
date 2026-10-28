import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2484 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2484 = true := by
  decide +kernel

theorem tot2484 : totK PA10K2 A10K2.t2484 = [0, 0, 14257594719, 1239043987545, 2392537604541, 877297603950, 63645606988, 0, 0, 0] := by
  decide +kernel

theorem rows2485 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2485 = true := by
  decide +kernel

theorem tot2485 : totK PA10K2 A10K2.t2485 = [482054232543, 1456573791262, 1397470978729, 411028566019, 368945387844, 501181406265, 128644302662, 5676195732, 0, 0] := by
  decide +kernel

theorem rows2486 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2486 = true := by
  decide +kernel

theorem tot2486 : totK PA10K2 A10K2.t2486 = [378150862450, 1727180881551, 2102332512276, 700371892553, 49663407621, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2487 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2487 = true := by
  decide +kernel

theorem tot2487 : totK PA10K2 A10K2.t2487 = [0, 539078877193, 1972452222607, 1829630280897, 422520257205, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
