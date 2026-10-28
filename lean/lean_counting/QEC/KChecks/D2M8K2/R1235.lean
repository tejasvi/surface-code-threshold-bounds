import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4940 = true := by
  decide +kernel

theorem tot4940 : totK PD2M8K2 D2M8K2.t4940 = [0, 177086449974, 446556346949, 254434087916, 20014507631, 0, 0, 0] := by
  decide +kernel

theorem rows4941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4941 = true := by
  decide +kernel

theorem tot4941 : totK PD2M8K2 D2M8K2.t4941 = [0, 68371975852, 347704585888, 393570051597, 79078368156, 1164319620, 0, 0] := by
  decide +kernel

theorem rows4942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4942 = true := by
  decide +kernel

theorem tot4942 : totK PD2M8K2 D2M8K2.t4942 = [0, 0, 206219002907, 495684815721, 164249070929, 9404247146, 0, 0] := by
  decide +kernel

theorem rows4943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4943 = true := by
  decide +kernel

theorem tot4943 : totK PD2M8K2 D2M8K2.t4943 = [0, 154627715334, 433534772008, 274372077074, 41827051028, 2481160468, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
