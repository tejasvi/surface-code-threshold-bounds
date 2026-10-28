import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2376 = true := by
  decide +kernel

theorem tot2376 : totK PD2M8K2 D2M8K2.t2376 = [0, 81852631826, 313584417960, 385541382169, 102554522628, 3581949829, 0, 0] := by
  decide +kernel

theorem rows2377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2377 = true := by
  decide +kernel

theorem tot2377 : totK PD2M8K2 D2M8K2.t2377 = [0, 175332109500, 483161687463, 243178192149, 12936563004, 0, 0, 0] := by
  decide +kernel

theorem rows2378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2378 = true := by
  decide +kernel

theorem tot2378 : totK PD2M8K2 D2M8K2.t2378 = [0, 65044701910, 342297643001, 397530475842, 76483653502, 1096505104, 0, 0] := by
  decide +kernel

theorem rows2379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2379 = true := by
  decide +kernel

theorem tot2379 : totK PD2M8K2 D2M8K2.t2379 = [0, 85201814089, 319597366474, 378988274264, 103767325805, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
