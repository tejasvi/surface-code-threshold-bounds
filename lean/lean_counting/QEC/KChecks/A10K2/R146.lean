import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows584 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t584 = true := by
  decide +kernel

theorem tot584 : totK PA10K2 A10K2.t584 = [0, 350712538393, 1235762656007, 1743348448894, 1105690349422, 195821153372, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows585 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t585 = true := by
  decide +kernel

theorem tot585 : totK PA10K2 A10K2.t585 = [0, 495973127102, 1890873703068, 1864211469646, 447672690548, 26386655430, 0, 0, 0, 0] := by
  decide +kernel

theorem rows586 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t586 = true := by
  decide +kernel

theorem tot586 : totK PA10K2 A10K2.t586 = [0, 0, 916324489053, 2368330802998, 1239725135570, 112069967990, 0, 0, 0, 0] := by
  decide +kernel

theorem rows587 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t587 = true := by
  decide +kernel

theorem tot587 : totK PA10K2 A10K2.t587 = [0, 0, 464978513806, 1808852629452, 1846554208408, 471160282650, 31193230065, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
