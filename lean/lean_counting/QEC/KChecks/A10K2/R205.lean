import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows820 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t820 = true := by
  decide +kernel

theorem tot820 : totK PA10K2 A10K2.t820 = [0, 532074575926, 2005001034135, 2042961024062, 479964559122, 12855574250, 0, 0, 0, 0] := by
  decide +kernel

theorem rows821 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t821 = true := by
  decide +kernel

theorem tot821 : totK PA10K2 A10K2.t821 = [0, 591520450209, 1866651043937, 1837313150937, 659456064701, 68676968663, 0, 0, 0, 0] := by
  decide +kernel

theorem rows822 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t822 = true := by
  decide +kernel

theorem tot822 : totK PA10K2 A10K2.t822 = [0, 0, 812167844858, 2282494507147, 1619958988966, 279632228845, 6904928264, 0, 0, 0] := by
  decide +kernel

theorem rows823 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t823 = true := by
  decide +kernel

theorem tot823 : totK PA10K2 A10K2.t823 = [0, 482081578581, 1673912602588, 1963242254226, 778591304376, 70663383760, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
