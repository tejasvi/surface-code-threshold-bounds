import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2580 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2580 = true := by
  decide +kernel

theorem tot2580 : totK PA10K2 A10K2.t2580 = [0, 442221634930, 1770570446206, 2042296518032, 613994834125, 40470591736, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2581 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2581 = true := by
  decide +kernel

theorem tot2581 : totK PA10K2 A10K2.t2581 = [0, 0, 497437902297, 1913927925574, 1783555683911, 424267941850, 25565504801, 0, 0, 0] := by
  decide +kernel

theorem rows2582 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2582 = true := by
  decide +kernel

theorem tot2582 : totK PA10K2 A10K2.t2582 = [0, 483560162552, 1729585959117, 1790807842921, 685689944964, 118470899485, 5517381808, 0, 0, 0] := by
  decide +kernel

theorem rows2583 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2583 = true := by
  decide +kernel

theorem tot2583 : totK PA10K2 A10K2.t2583 = [0, 297849083520, 1516059512462, 2162463735594, 710125546641, 38254334585, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
