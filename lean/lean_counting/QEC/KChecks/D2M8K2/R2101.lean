import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8404 = true := by
  decide +kernel

theorem tot8404 : totK PD2M8K2 D2M8K2.t8404 = [0, 0, 209723539290, 483585737064, 156820297907, 7362961718, 0, 0] := by
  decide +kernel

theorem rows8405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8405 = true := by
  decide +kernel

theorem tot8405 : totK PD2M8K2 D2M8K2.t8405 = [0, 0, 193083194883, 472312234483, 209157597019, 14510083306, 0, 0] := by
  decide +kernel

theorem rows8406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8406 = true := by
  decide +kernel

theorem tot8406 : totK PD2M8K2 D2M8K2.t8406 = [0, 0, 187631429944, 456083299706, 208973253948, 16632994142, 0, 0] := by
  decide +kernel

theorem rows8407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8407 = true := by
  decide +kernel

theorem tot8407 : totK PD2M8K2 D2M8K2.t8407 = [0, 0, 140166646783, 440723838222, 267693960422, 23182997144, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
