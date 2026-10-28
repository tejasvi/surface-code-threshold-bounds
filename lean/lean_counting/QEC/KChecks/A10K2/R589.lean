import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2356 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2356 = true := by
  decide +kernel

theorem tot2356 : totK PA10K2 A10K2.t2356 = [0, 0, 658921244530, 2010588031793, 1710405583869, 409016838713, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows2357 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2357 = true := by
  decide +kernel

theorem tot2357 : totK PA10K2 A10K2.t2357 = [0, 238785603865, 1050611792854, 1834004857791, 1268457272122, 219736888942, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows2358 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2358 = true := by
  decide +kernel

theorem tot2358 : totK PA10K2 A10K2.t2358 = [0, 583317622402, 1950252648849, 1771378140001, 451641391154, 31941609474, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2359 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2359 = true := by
  decide +kernel

theorem tot2359 : totK PA10K2 A10K2.t2359 = [0, 0, 942663342402, 2342604565825, 1235169721504, 113491970078, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
