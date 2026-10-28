import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5460 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5460 = true := by
  decide +kernel

theorem tot5460 : totK PA10K2 A10K2.t5460 = [0, 310980684517, 1223426605338, 1813498227358, 1176976814549, 217835182147, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows5461 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5461 = true := by
  decide +kernel

theorem tot5461 : totK PA10K2 A10K2.t5461 = [0, 459708423507, 1815555808106, 1975319970179, 530825388915, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5462 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5462 = true := by
  decide +kernel

theorem tot5462 : totK PA10K2 A10K2.t5462 = [0, 0, 767872643668, 2281808000501, 1508400568092, 169314849330, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5463 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5463 = true := by
  decide +kernel

theorem tot5463 : totK PA10K2 A10K2.t5463 = [0, 554803763168, 1823627380194, 1791188118771, 658244135909, 132560125429, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
