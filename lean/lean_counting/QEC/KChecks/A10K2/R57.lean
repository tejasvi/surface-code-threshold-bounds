import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows228 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t228 = true := by
  decide +kernel

theorem tot228 : totK PA10K2 A10K2.t228 = [0, 309893393367, 1473018754885, 2181496955774, 926858147305, 77103908526, 0, 0, 0, 0] := by
  decide +kernel

theorem rows229 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t229 = true := by
  decide +kernel

theorem tot229 : totK PA10K2 A10K2.t229 = [0, 0, 594168236395, 2065057361897, 2043192121236, 398822253610, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows230 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t230 = true := by
  decide +kernel

theorem tot230 : totK PA10K2 A10K2.t230 = [0, 0, 381977790864, 1549250155500, 2067813314981, 828213567215, 66212171727, 0, 0, 0] := by
  decide +kernel

theorem rows231 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t231 = true := by
  decide +kernel

theorem tot231 : totK PA10K2 A10K2.t231 = [0, 0, 472975527039, 1917250371645, 1981369793117, 448529057740, 12350643961, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
