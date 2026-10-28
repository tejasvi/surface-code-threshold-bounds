import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5340 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5340 = true := by
  decide +kernel

theorem tot5340 : totK PA10K2 A10K2.t5340 = [0, 0, 583342381484, 2014073440175, 1958545079257, 463744018350, 12855574250, 0, 0, 0] := by
  decide +kernel

theorem rows5341 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5341 = true := by
  decide +kernel

theorem tot5341 : totK PA10K2 A10K2.t5341 = [0, 0, 474272902674, 1717213840580, 1885841295726, 699584197338, 68750515780, 0, 0, 0] := by
  decide +kernel

theorem rows5342 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5342 = true := by
  decide +kernel

theorem tot5342 : totK PA10K2 A10K2.t5342 = [0, 0, 305330155506, 1444752195185, 2144056414951, 938893850730, 76381823220, 0, 0, 0] := by
  decide +kernel

theorem rows5343 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5343 = true := by
  decide +kernel

theorem tot5343 : totK PA10K2 A10K2.t5343 = [0, 0, 177094761672, 993232378470, 2044654755040, 1443269615333, 265297957570, 6904928264, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
