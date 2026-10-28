import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2800 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2800 = true := by
  decide +kernel

theorem tot2800 : totK PA10K2 A10K2.t2800 = [0, 0, 111994467761, 905236664507, 1957931882456, 1394374636074, 342196349010, 25239774317, 0, 0] := by
  decide +kernel

theorem rows2801 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2801 = true := by
  decide +kernel

theorem tot2801 : totK PA10K2 A10K2.t2801 = [0, 0, 286314852903, 1213861220653, 1788343672174, 1113850280315, 195770986900, 5365973533, 0, 0] := by
  decide +kernel

theorem rows2802 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2802 = true := by
  decide +kernel

theorem tot2802 : totK PA10K2 A10K2.t2802 = [0, 0, 267214149505, 1505076771516, 2145542698394, 713272353966, 52324980649, 0, 0, 0] := by
  decide +kernel

theorem rows2803 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2803 = true := by
  decide +kernel

theorem tot2803 : totK PA10K2 A10K2.t2803 = [0, 0, 293731123861, 1233502867163, 1903734970781, 1050063816890, 164365330957, 5528811039, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
