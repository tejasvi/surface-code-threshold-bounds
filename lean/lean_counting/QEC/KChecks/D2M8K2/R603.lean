import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2412 = true := by
  decide +kernel

theorem tot2412 : totK PD2M8K2 D2M8K2.t2412 = [0, 38189920222, 318934802461, 444619042091, 94643502412, 1198073392, 0, 0] := by
  decide +kernel

theorem rows2413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2413 = true := by
  decide +kernel

theorem tot2413 : totK PD2M8K2 D2M8K2.t2413 = [0, 0, 211863981073, 476171552211, 180947654057, 7715358911, 0, 0] := by
  decide +kernel

theorem rows2414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2414 = true := by
  decide +kernel

theorem tot2414 : totK PD2M8K2 D2M8K2.t2414 = [0, 176646720806, 466171278686, 259872551796, 29487393215, 0, 0, 0] := by
  decide +kernel

theorem rows2415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2415 = true := by
  decide +kernel

theorem tot2415 : totK PD2M8K2 D2M8K2.t2415 = [0, 177080075921, 458490923831, 260971039520, 18276815561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
