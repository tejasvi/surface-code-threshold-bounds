import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6100 = true := by
  decide +kernel

theorem tot6100 : totK PA10K2 A10K2.t6100 = [0, 0, 469442925179, 1703921287140, 1949118379040, 694231029768, 55284946814, 0, 0, 0] := by
  decide +kernel

theorem rows6101 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6101 = true := by
  decide +kernel

theorem tot6101 : totK PA10K2 A10K2.t6101 = [0, 0, 305339024646, 1514448731225, 2212990547530, 865416865016, 62455608302, 0, 0, 0] := by
  decide +kernel

theorem rows6102 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6102 = true := by
  decide +kernel

theorem tot6102 : totK PA10K2 A10K2.t6102 = [0, 0, 284030005396, 1231844055178, 1959146977252, 1229339873171, 210190865443, 6318667960, 0, 0] := by
  decide +kernel

theorem rows6103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6103 = true := by
  decide +kernel

theorem tot6103 : totK PA10K2 A10K2.t6103 = [0, 0, 399594747110, 1753470911041, 2199085400270, 683914297871, 24993131327, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
