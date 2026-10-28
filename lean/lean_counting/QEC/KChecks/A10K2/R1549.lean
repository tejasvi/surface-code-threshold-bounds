import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6196 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6196 = true := by
  decide +kernel

theorem tot6196 : totK PA10K2 A10K2.t6196 = [0, 400574669161, 1230279077887, 1592769775966, 1253662779988, 419928681969, 29791859037, 0, 0, 0] := by
  decide +kernel

theorem rows6197 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6197 = true := by
  decide +kernel

theorem tot6197 : totK PA10K2 A10K2.t6197 = [0, 361770035178, 1643124393081, 2067844486942, 724311588182, 56693832332, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6198 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6198 = true := by
  decide +kernel

theorem tot6198 : totK PA10K2 A10K2.t6198 = [0, 0, 502951896176, 1818262457608, 1832061982940, 476019217556, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows6199 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6199 = true := by
  decide +kernel

theorem tot6199 : totK PA10K2 A10K2.t6199 = [0, 523679276711, 1733144547649, 1891768471466, 709975147436, 65487265550, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
