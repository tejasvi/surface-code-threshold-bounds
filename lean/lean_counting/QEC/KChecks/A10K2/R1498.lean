import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5992 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5992 = true := by
  decide +kernel

theorem tot5992 : totK PA10K2 A10K2.t5992 = [441538332422, 1760423585783, 1974792803547, 555979507011, 32040661968, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5993 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5993 = true := by
  decide +kernel

theorem tot5993 : totK PA10K2 A10K2.t5993 = [159080905221, 963820793774, 1898091011139, 1437653757938, 362390524217, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5994 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5994 = true := by
  decide +kernel

theorem tot5994 : totK PA10K2 A10K2.t5994 = [279438172082, 1180618535903, 1888628312685, 1250898702707, 219372496472, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5995 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5995 = true := by
  decide +kernel

theorem tot5995 : totK PA10K2 A10K2.t5995 = [283429591508, 1543554204697, 2185343021554, 765776252422, 54149635648, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
