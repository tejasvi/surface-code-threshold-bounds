import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6096 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6096 = true := by
  decide +kernel

theorem tot6096 : totK PA10K2 A10K2.t6096 = [0, 281717535487, 1123860596948, 1824322236829, 1451686059963, 349091571163, 12219140272, 0, 0, 0] := by
  decide +kernel

theorem rows6097 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6097 = true := by
  decide +kernel

theorem tot6097 : totK PA10K2 A10K2.t6097 = [0, 477395108862, 1796888271510, 2025558451887, 635924616941, 33480676086, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6098 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6098 = true := by
  decide +kernel

theorem tot6098 : totK PA10K2 A10K2.t6098 = [0, 122956571035, 1003235531998, 2159377100320, 1470339133679, 237046633408, 6772895877, 0, 0, 0] := by
  decide +kernel

theorem rows6099 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6099 = true := by
  decide +kernel

theorem tot6099 : totK PA10K2 A10K2.t6099 = [0, 0, 597364730005, 2047758081074, 1970871855609, 439613298859, 12773195692, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
