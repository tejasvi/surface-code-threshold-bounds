import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5328 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5328 = true := by
  decide +kernel

theorem tot5328 : totK PA10K2 A10K2.t5328 = [0, 0, 0, 461417741280, 1789742103505, 1786470130634, 436968260938, 25239774317, 0, 0] := by
  decide +kernel

theorem rows5329 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5329 = true := by
  decide +kernel

theorem tot5329 : totK PA10K2 A10K2.t5329 = [0, 0, 418471038443, 1642035682099, 1973808268658, 745167651543, 103088633770, 5410721913, 0, 0] := by
  decide +kernel

theorem rows5330 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5330 = true := by
  decide +kernel

theorem tot5330 : totK PA10K2 A10K2.t5330 = [0, 0, 138992330854, 1222257129481, 2237907338535, 961145004870, 85757362997, 0, 0, 0] := by
  decide +kernel

theorem rows5331 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5331 = true := by
  decide +kernel

theorem tot5331 : totK PA10K2 A10K2.t5331 = [0, 0, 486094728343, 1673225935255, 1844045372036, 800666423648, 134236938833, 5546304973, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
