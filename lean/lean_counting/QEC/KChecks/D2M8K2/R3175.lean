import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12700 = true := by
  decide +kernel

theorem tot12700 : totK PD2M8K2 D2M8K2.t12700 = [0, 0, 36500538194, 233829343520, 413901706897, 162959599933, 11986244008, 0] := by
  decide +kernel

theorem rows12701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12701 = true := by
  decide +kernel

theorem tot12701 : totK PD2M8K2 D2M8K2.t12701 = [0, 0, 190049968547, 462779627053, 245871657069, 18659034136, 0, 0] := by
  decide +kernel

theorem rows12702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12702 = true := by
  decide +kernel

theorem tot12702 : totK PD2M8K2 D2M8K2.t12702 = [0, 0, 187706488695, 452935405409, 234143074497, 17104814242, 0, 0] := by
  decide +kernel

theorem rows12703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12703 = true := by
  decide +kernel

theorem tot12703 : totK PD2M8K2 D2M8K2.t12703 = [0, 0, 19228354030, 341191182680, 455903017864, 77857058051, 1096505104, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
