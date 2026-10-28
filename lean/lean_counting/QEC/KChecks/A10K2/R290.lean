import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1160 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1160 = true := by
  decide +kernel

theorem tot1160 : totK PA10K2 A10K2.t1160 = [0, 0, 465857377343, 1862767893769, 1888025300253, 440623685395, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows1161 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1161 = true := by
  decide +kernel

theorem tot1161 : totK PA10K2 A10K2.t1161 = [0, 425141663883, 1678330363357, 1862491077286, 646059440433, 104882760309, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows1162 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1162 = true := by
  decide +kernel

theorem tot1162 : totK PA10K2 A10K2.t1162 = [0, 109458229214, 725591498042, 1844220606732, 1518596270965, 306538974049, 11427838733, 0, 0, 0] := by
  decide +kernel

theorem rows1163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1163 = true := by
  decide +kernel

theorem tot1163 : totK PA10K2 A10K2.t1163 = [0, 465759800139, 1645170501969, 1800978067833, 610087934816, 52232171148, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
