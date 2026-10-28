import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5528 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5528 = true := by
  decide +kernel

theorem tot5528 : totK PA10K2 A10K2.t5528 = [0, 114484931651, 800391514456, 2002466454366, 1703956134367, 378240660820, 13360781053, 0, 0, 0] := by
  decide +kernel

theorem rows5529 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5529 = true := by
  decide +kernel

theorem tot5529 : totK PA10K2 A10K2.t5529 = [0, 518325263045, 1863439310607, 1920599864633, 533305362874, 32616509612, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5530 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5530 = true := by
  decide +kernel

theorem tot5530 : totK PA10K2 A10K2.t5530 = [0, 151085706990, 1103284576987, 2130441619245, 1343320658160, 269917869526, 20300850681, 0, 0, 0] := by
  decide +kernel

theorem rows5531 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5531 = true := by
  decide +kernel

theorem tot5531 : totK PA10K2 A10K2.t5531 = [0, 210098550300, 955919014927, 1851722416688, 1514679775317, 327387877884, 11376377689, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
