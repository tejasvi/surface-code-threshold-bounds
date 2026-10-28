import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7476 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7476 = true := by
  decide +kernel

theorem tot7476 : totK PA10K2 A10K2.t7476 = [0, 0, 609977757965, 1995363616506, 1872234301667, 521973276158, 33056434722, 0, 0, 0] := by
  decide +kernel

theorem rows7477 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7477 = true := by
  decide +kernel

theorem tot7477 : totK PA10K2 A10K2.t7477 = [0, 0, 0, 829188366340, 2419530638110, 1673886514441, 218703826163, 0, 0, 0] := by
  decide +kernel

theorem rows7478 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7478 = true := by
  decide +kernel

theorem tot7478 : totK PA10K2 A10K2.t7478 = [0, 0, 0, 492921413856, 1770224770093, 1995823152616, 638379379908, 41062513076, 0, 0] := by
  decide +kernel

theorem rows7479 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7479 = true := by
  decide +kernel

theorem tot7479 : totK PA10K2 A10K2.t7479 = [0, 0, 0, 437800125765, 1762555977947, 1911624488583, 534946261192, 32523532663, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
