import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1240 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1240 = true := by
  decide +kernel

theorem tot1240 : totK PA10K2 A10K2.t1240 = [0, 0, 484640629618, 1823956207981, 1919610131753, 528560071579, 32523532663, 0, 0, 0] := by
  decide +kernel

theorem rows1241 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1241 = true := by
  decide +kernel

theorem tot1241 : totK PA10K2 A10K2.t1241 = [0, 0, 554913666366, 1866188899060, 1830790200001, 469463127477, 31936107789, 0, 0, 0] := by
  decide +kernel

theorem rows1242 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1242 = true := by
  decide +kernel

theorem tot1242 : totK PA10K2 A10K2.t1242 = [0, 0, 129700914100, 1341858818195, 2318452497789, 825866380766, 50305391989, 0, 0, 0] := by
  decide +kernel

theorem rows1243 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1243 = true := by
  decide +kernel

theorem tot1243 : totK PA10K2 A10K2.t1243 = [0, 313543329064, 1097518925268, 1308080500648, 1034692241348, 749767493130, 162289770064, 6121173289, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
