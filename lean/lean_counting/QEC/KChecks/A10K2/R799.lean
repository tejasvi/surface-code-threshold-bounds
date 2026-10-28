import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3196 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3196 = true := by
  decide +kernel

theorem tot3196 : totK PA10K2 A10K2.t3196 = [0, 0, 478804892860, 1831798597179, 1922662470798, 504543508877, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows3197 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3197 = true := by
  decide +kernel

theorem tot3197 : totK PA10K2 A10K2.t3197 = [0, 476246592928, 1636860863955, 1759290608210, 690535555491, 83775891897, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3198 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3198 = true := by
  decide +kernel

theorem tot3198 : totK PA10K2 A10K2.t3198 = [0, 298263154340, 1440579342970, 2045294001631, 773551227932, 53385992088, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3199 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3199 = true := by
  decide +kernel

theorem tot3199 : totK PA10K2 A10K2.t3199 = [0, 0, 724467769194, 2123044289808, 1510614757088, 254157072984, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
