import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows844 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t844 = true := by
  decide +kernel

theorem tot844 : totK PA10K2 A10K2.t844 = [0, 306766947263, 1492599879379, 2179811230068, 982054329167, 96629334496, 0, 0, 0, 0] := by
  decide +kernel

theorem rows845 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t845 = true := by
  decide +kernel

theorem tot845 : totK PA10K2 A10K2.t845 = [0, 305238687968, 1248394403899, 1970392673876, 1293069793875, 243513627372, 7007974415, 0, 0, 0] := by
  decide +kernel

theorem rows846 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t846 = true := by
  decide +kernel

theorem tot846 : totK PA10K2 A10K2.t846 = [0, 481291611570, 1795241426734, 2000590219404, 610199502148, 38083269778, 0, 0, 0, 0] := by
  decide +kernel

theorem rows847 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t847 = true := by
  decide +kernel

theorem tot847 : totK PA10K2 A10K2.t847 = [0, 0, 707652415782, 2072969646831, 1708229868931, 408396790400, 25660650750, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
