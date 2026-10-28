import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6256 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6256 = true := by
  decide +kernel

theorem tot6256 : totK PA10K2 A10K2.t6256 = [0, 433044328481, 1823144203250, 2186062382391, 682414384601, 38876198219, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6257 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6257 = true := by
  decide +kernel

theorem tot6257 : totK PA10K2 A10K2.t6257 = [0, 0, 683247370727, 2144643067312, 1819531115820, 386879254865, 12692412833, 0, 0, 0] := by
  decide +kernel

theorem rows6258 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6258 = true := by
  decide +kernel

theorem tot6258 : totK PA10K2 A10K2.t6258 = [0, 552204907645, 1799439286691, 1841751838591, 723588471049, 75836120031, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6259 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6259 = true := by
  decide +kernel

theorem tot6259 : totK PA10K2 A10K2.t6259 = [0, 330854518425, 1567602448736, 2199787565797, 880877067687, 68663521283, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
