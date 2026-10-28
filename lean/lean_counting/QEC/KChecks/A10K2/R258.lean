import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1032 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1032 = true := by
  decide +kernel

theorem tot1032 : totK PA10K2 A10K2.t1032 = [0, 0, 84539485306, 914699494132, 2140600902463, 1565241161031, 271379366492, 7047025452, 0, 0] := by
  decide +kernel

theorem rows1033 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1033 = true := by
  decide +kernel

theorem tot1033 : totK PA10K2 A10K2.t1033 = [0, 0, 322384795560, 1461459960411, 2143753203342, 916540480739, 73845105913, 0, 0, 0] := by
  decide +kernel

theorem rows1034 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1034 = true := by
  decide +kernel

theorem tot1034 : totK PA10K2 A10K2.t1034 = [0, 0, 543851517819, 1961477380312, 1954020438011, 523971176981, 18513647723, 0, 0, 0] := by
  decide +kernel

theorem rows1035 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1035 = true := by
  decide +kernel

theorem tot1035 : totK PA10K2 A10K2.t1035 = [0, 0, 0, 735404172885, 2216757563964, 1719403097999, 266859478888, 6066958478, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
