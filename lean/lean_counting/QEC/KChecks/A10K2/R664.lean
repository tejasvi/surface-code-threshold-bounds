import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2656 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2656 = true := by
  decide +kernel

theorem tot2656 : totK PA10K2 A10K2.t2656 = [0, 378150862450, 1727180881551, 2102332512276, 700371892553, 47533210600, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2657 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2657 = true := by
  decide +kernel

theorem tot2657 : totK PA10K2 A10K2.t2657 = [0, 0, 539078877193, 1972452222607, 1829146098261, 422520257205, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows2658 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2658 = true := by
  decide +kernel

theorem tot2658 : totK PA10K2 A10K2.t2658 = [0, 377824520111, 1414662744529, 1752248919765, 984765756576, 183883342592, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows2659 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2659 = true := by
  decide +kernel

theorem tot2659 : totK PA10K2 A10K2.t2659 = [0, 365113414197, 1626124814287, 2051897595035, 654305403163, 47503842097, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
