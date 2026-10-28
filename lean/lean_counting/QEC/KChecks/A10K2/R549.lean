import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2196 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2196 = true := by
  decide +kernel

theorem tot2196 : totK PA10K2 A10K2.t2196 = [0, 431788502220, 1755318307133, 2138038306320, 689304060472, 38670148117, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2197 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2197 = true := by
  decide +kernel

theorem tot2197 : totK PA10K2 A10K2.t2197 = [625736493037, 1922074776356, 1653848621556, 569254499692, 233526811873, 37674658091, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2198 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2198 = true := by
  decide +kernel

theorem tot2198 : totK PA10K2 A10K2.t2198 = [0, 744056318776, 2180154218681, 1671451018823, 340425351042, 19474173409, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2199 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2199 = true := by
  decide +kernel

theorem tot2199 : totK PA10K2 A10K2.t2199 = [404541561496, 1585544747437, 2012415135716, 878006916626, 86853291742, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
