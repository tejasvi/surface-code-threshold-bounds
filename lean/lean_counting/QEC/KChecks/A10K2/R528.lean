import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2112 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2112 = true := by
  decide +kernel

theorem tot2112 : totK PA10K2 A10K2.t2112 = [344302994732, 1289558143981, 1807861097833, 1041636864292, 167086268594, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2113 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2113 = true := by
  decide +kernel

theorem tot2113 : totK PA10K2 A10K2.t2113 = [394514376918, 1659921719902, 1971719827975, 680339628921, 53383856823, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2114 = true := by
  decide +kernel

theorem tot2114 : totK PA10K2 A10K2.t2114 = [0, 746087980111, 2184762259704, 1535731749987, 258251384459, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2115 = true := by
  decide +kernel

theorem tot2115 : totK PA10K2 A10K2.t2115 = [0, 443310147685, 1786957203905, 1941842426481, 516560416455, 31222411477, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
