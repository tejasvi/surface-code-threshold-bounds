import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows224 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t224 = true := by
  decide +kernel

theorem tot224 : totK PA10K2 A10K2.t224 = [0, 293873915135, 1166015428642, 1840771671204, 1237366896416, 202162471992, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows225 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t225 = true := by
  decide +kernel

theorem tot225 : totK PA10K2 A10K2.t225 = [0, 425334562625, 1658198613221, 1881918784124, 591456925433, 37026429097, 0, 0, 0, 0] := by
  decide +kernel

theorem rows226 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t226 = true := by
  decide +kernel

theorem tot226 : totK PA10K2 A10K2.t226 = [0, 0, 930175578190, 2351182158651, 1195667884010, 89296183373, 0, 0, 0, 0] := by
  decide +kernel

theorem rows227 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t227 = true := by
  decide +kernel

theorem tot227 : totK PA10K2 A10K2.t227 = [0, 474063995440, 1597994275915, 1792067082938, 887411708147, 170665733916, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
