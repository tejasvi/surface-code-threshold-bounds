import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2696 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2696 = true := by
  decide +kernel

theorem tot2696 : totK PA10K2 A10K2.t2696 = [0, 278580461261, 1153197155980, 1874958812295, 1219237609263, 206593729233, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows2697 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2697 = true := by
  decide +kernel

theorem tot2697 : totK PA10K2 A10K2.t2697 = [0, 500003266873, 1736638858187, 1859044837103, 637690717160, 52230035883, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2698 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2698 = true := by
  decide +kernel

theorem tot2698 : totK PA10K2 A10K2.t2698 = [0, 0, 1034185285941, 2411068926061, 1192228024381, 107172403957, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2699 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2699 = true := by
  decide +kernel

theorem tot2699 : totK PA10K2 A10K2.t2699 = [0, 266424507814, 1204837700322, 1925161195454, 1158492599803, 214259699086, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
