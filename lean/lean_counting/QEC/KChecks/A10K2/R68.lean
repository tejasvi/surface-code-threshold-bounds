import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows272 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t272 = true := by
  decide +kernel

theorem tot272 : totK PA10K2 A10K2.t272 = [0, 0, 0, 405942101785, 1678093791951, 2019851794521, 666286470835, 53844901745, 0, 0] := by
  decide +kernel

theorem rows273 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t273 = true := by
  decide +kernel

theorem tot273 : totK PA10K2 A10K2.t273 = [0, 0, 0, 432512310136, 1794324411606, 1889291098125, 520401706790, 34193440607, 0, 0] := by
  decide +kernel

theorem rows274 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t274 = true := by
  decide +kernel

theorem tot274 : totK PA10K2 A10K2.t274 = [0, 0, 0, 0, 546391999996, 1915669947246, 1665383192613, 394932850182, 25239774317, 0] := by
  decide +kernel

theorem rows275 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t275 = true := by
  decide +kernel

theorem tot275 : totK PA10K2 A10K2.t275 = [0, 0, 0, 369094636529, 1467549572407, 1843780521580, 843803318306, 137308631461, 5365973533, 0] := by
  decide +kernel

end QECKChecks.A10K2
