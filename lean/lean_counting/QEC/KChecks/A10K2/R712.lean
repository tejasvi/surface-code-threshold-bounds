import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2848 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2848 = true := by
  decide +kernel

theorem tot2848 : totK PA10K2 A10K2.t2848 = [0, 308525764274, 1332580088226, 1980708110486, 1102560498181, 191205203086, 6904928264, 0, 0, 0] := by
  decide +kernel

theorem rows2849 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2849 = true := by
  decide +kernel

theorem tot2849 : totK PA10K2 A10K2.t2849 = [0, 495583288092, 1898552733251, 2076654272460, 552439677516, 18905659125, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2850 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2850 = true := by
  decide +kernel

theorem tot2850 : totK PA10K2 A10K2.t2850 = [0, 0, 751610180847, 2207029408442, 1682909058974, 282545979453, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows2851 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2851 = true := by
  decide +kernel

theorem tot2851 : totK PA10K2 A10K2.t2851 = [0, 534421757282, 1834274241082, 1876581528497, 634352906985, 59041540305, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
