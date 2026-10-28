import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12652 = true := by
  decide +kernel

theorem tot12652 : totK PD2M8K2 D2M8K2.t12652 = [0, 0, 0, 216453564644, 464729160993, 174126640078, 12158747742, 0] := by
  decide +kernel

theorem rows12653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12653 = true := by
  decide +kernel

theorem tot12653 : totK PD2M8K2 D2M8K2.t12653 = [0, 0, 0, 206225803444, 467927062120, 167725128059, 9609506048, 0] := by
  decide +kernel

theorem rows12654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12654 = true := by
  decide +kernel

theorem tot12654 : totK PD2M8K2 D2M8K2.t12654 = [0, 0, 0, 194765379808, 473016966101, 182027522439, 12242580035, 0] := by
  decide +kernel

theorem rows12655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12655 = true := by
  decide +kernel

theorem tot12655 : totK PD2M8K2 D2M8K2.t12655 = [0, 0, 0, 314471928849, 494909494348, 96016277855, 1369587937, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
