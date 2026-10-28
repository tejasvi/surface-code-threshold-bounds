import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12584 = true := by
  decide +kernel

theorem tot12584 : totK PD2M8K2 D2M8K2.t12584 = [0, 172332080960, 463078778622, 261261601087, 22333959257, 0, 0, 0] := by
  decide +kernel

theorem rows12585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12585 = true := by
  decide +kernel

theorem tot12585 : totK PD2M8K2 D2M8K2.t12585 = [0, 180114736652, 465285738089, 244619792066, 17034666133, 0, 0, 0] := by
  decide +kernel

theorem rows12586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12586 = true := by
  decide +kernel

theorem tot12586 : totK PD2M8K2 D2M8K2.t12586 = [0, 0, 303725513392, 501915461502, 95333084860, 1096505104, 0, 0] := by
  decide +kernel

theorem rows12587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12587 = true := by
  decide +kernel

theorem tot12587 : totK PD2M8K2 D2M8K2.t12587 = [0, 0, 274511326172, 500595973238, 124635077563, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
