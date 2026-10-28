import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9308 = true := by
  decide +kernel

theorem tot9308 : totK PD2M8K2 D2M8K2.t9308 = [0, 313362244747, 518016599642, 90490184801, 1069412848, 0, 0, 0] := by
  decide +kernel

theorem rows9309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9309 = true := by
  decide +kernel

theorem tot9309 : totK PD2M8K2 D2M8K2.t9309 = [0, 173081314783, 481629702376, 212552095112, 10093459964, 0, 0, 0] := by
  decide +kernel

theorem rows9310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9310 = true := by
  decide +kernel

theorem tot9310 : totK PD2M8K2 D2M8K2.t9310 = [0, 184366374152, 456759332723, 222588842506, 13892812787, 0, 0, 0] := by
  decide +kernel

theorem rows9311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9311 = true := by
  decide +kernel

theorem tot9311 : totK PD2M8K2 D2M8K2.t9311 = [0, 53217553446, 338108646775, 377811481980, 65020973887, 1138244013, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
