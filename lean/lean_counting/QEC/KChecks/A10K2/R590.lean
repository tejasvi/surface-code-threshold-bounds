import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2360 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2360 = true := by
  decide +kernel

theorem tot2360 : totK PA10K2 A10K2.t2360 = [0, 0, 483936842680, 1834336720839, 1795130727262, 468200857234, 31558137809, 0, 0, 0] := by
  decide +kernel

theorem rows2361 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2361 = true := by
  decide +kernel

theorem tot2361 : totK PA10K2 A10K2.t2361 = [0, 0, 472117106666, 1831833848340, 1947420712722, 491686732012, 26944146327, 0, 0, 0] := by
  decide +kernel

theorem rows2362 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2362 = true := by
  decide +kernel

theorem tot2362 : totK PA10K2 A10K2.t2362 = [0, 0, 509174647242, 1843314246579, 1977173399527, 539401093062, 18754734689, 0, 0, 0] := by
  decide +kernel

theorem rows2363 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2363 = true := by
  decide +kernel

theorem tot2363 : totK PA10K2 A10K2.t2363 = [0, 0, 469543783115, 1734336519630, 1791102630149, 484271080544, 44363554315, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
