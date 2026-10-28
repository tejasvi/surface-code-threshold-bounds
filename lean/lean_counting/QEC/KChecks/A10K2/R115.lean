import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows460 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t460 = true := by
  decide +kernel

theorem tot460 : totK PA10K2 A10K2.t460 = [0, 0, 676852237074, 2136735012480, 1613964949865, 257893870822, 6239800209, 0, 0, 0] := by
  decide +kernel

theorem rows461 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t461 = true := by
  decide +kernel

theorem tot461 : totK PA10K2 A10K2.t461 = [0, 0, 526181235765, 1824458731776, 1745479984238, 449840690474, 30637645759, 0, 0, 0] := by
  decide +kernel

theorem rows462 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t462 = true := by
  decide +kernel

theorem tot462 : totK PA10K2 A10K2.t462 = [0, 0, 0, 1014405953354, 2384621305422, 1047341906120, 90488860210, 0, 0, 0] := by
  decide +kernel

theorem rows463 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t463 = true := by
  decide +kernel

theorem tot463 : totK PA10K2 A10K2.t463 = [0, 510277227219, 1709467980483, 1580515859731, 575168536011, 329594728644, 101801049440, 5676195732, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
