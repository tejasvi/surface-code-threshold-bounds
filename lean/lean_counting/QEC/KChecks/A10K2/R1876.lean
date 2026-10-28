import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7504 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7504 = true := by
  decide +kernel

theorem tot7504 : totK PA10K2 A10K2.t7504 = [0, 372560096969, 1253627839856, 1279300947388, 666812561955, 798639465191, 458303640743, 49137922124, 0, 0] := by
  decide +kernel

theorem rows7505 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7505 = true := by
  decide +kernel

theorem tot7505 : totK PA10K2 A10K2.t7505 = [0, 469466733197, 1821114883446, 2018262219797, 557935009164, 16226811436, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7506 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7506 = true := by
  decide +kernel

theorem tot7506 : totK PA10K2 A10K2.t7506 = [0, 0, 581264391071, 1978722332232, 1781067399706, 425800152275, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows7507 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7507 = true := by
  decide +kernel

theorem tot7507 : totK PA10K2 A10K2.t7507 = [0, 347345712664, 1265744234034, 1788689758391, 1143769636950, 213254356425, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
