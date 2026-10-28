import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5344 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5344 = true := by
  decide +kernel

theorem tot5344 : totK PA10K2 A10K2.t5344 = [0, 0, 417175151754, 1777089885204, 2187447368740, 704342924881, 26484578482, 0, 0, 0] := by
  decide +kernel

theorem rows5345 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5345 = true := by
  decide +kernel

theorem tot5345 : totK PA10K2 A10K2.t5345 = [0, 0, 124060985525, 888332283058, 2061429357190, 1627646433519, 273222747194, 7047025452, 0, 0] := by
  decide +kernel

theorem rows5346 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5346 = true := by
  decide +kernel

theorem tot5346 : totK PA10K2 A10K2.t5346 = [0, 0, 508087552274, 1872580551624, 1985850179072, 575424038784, 23620721234, 0, 0, 0] := by
  decide +kernel

theorem rows5347 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5347 = true := by
  decide +kernel

theorem tot5347 : totK PA10K2 A10K2.t5347 = [0, 0, 224708113702, 1271844208708, 2205199524417, 1159207600840, 113417152791, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
