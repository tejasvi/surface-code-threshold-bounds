import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3116 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3116 = true := by
  decide +kernel

theorem tot3116 : totK PA10K2 A10K2.t3116 = [0, 0, 313050775879, 1521224662925, 2166749832879, 817435463881, 52133213346, 0, 0, 0] := by
  decide +kernel

theorem rows3117 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3117 = true := by
  decide +kernel

theorem tot3117 : totK PA10K2 A10K2.t3117 = [0, 0, 544749639382, 1894577410102, 1958294515844, 560770035871, 24664512981, 0, 0, 0] := by
  decide +kernel

theorem rows3118 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3118 = true := by
  decide +kernel

theorem tot3118 : totK PA10K2 A10K2.t3118 = [0, 289498769530, 1009050302610, 1527391089860, 1384328029169, 553627407610, 50555834002, 0, 0, 0] := by
  decide +kernel

theorem rows3119 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3119 = true := by
  decide +kernel

theorem tot3119 : totK PA10K2 A10K2.t3119 = [0, 436450538801, 1776197717709, 2078396368839, 713223401945, 51394862541, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
