import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13040 = true := by
  decide +kernel

theorem tot13040 : totK PD2M8K2 D2M8K2.t13040 = [0, 0, 200447642626, 485638221870, 185997814011, 6230706934, 0, 0] := by
  decide +kernel

theorem rows13041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13041 = true := by
  decide +kernel

theorem tot13041 : totK PD2M8K2 D2M8K2.t13041 = [0, 0, 87433260428, 367531467263, 351512097821, 60357017592, 1310285577, 0] := by
  decide +kernel

theorem rows13042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13042 = true := by
  decide +kernel

theorem tot13042 : totK PD2M8K2 D2M8K2.t13042 = [0, 0, 73502833985, 393847776174, 393652653959, 28151497242, 0, 0] := by
  decide +kernel

theorem rows13043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13043 = true := by
  decide +kernel

theorem tot13043 : totK PD2M8K2 D2M8K2.t13043 = [0, 0, 175963882562, 448811579491, 267524404065, 27434826853, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
