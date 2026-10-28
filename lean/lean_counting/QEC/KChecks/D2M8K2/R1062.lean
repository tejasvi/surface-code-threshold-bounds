import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4248 = true := by
  decide +kernel

theorem tot4248 : totK PD2M8K2 D2M8K2.t4248 = [0, 0, 0, 220116511263, 508685668448, 171560960542, 6825433439, 0] := by
  decide +kernel

theorem rows4249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4249 = true := by
  decide +kernel

theorem tot4249 : totK PD2M8K2 D2M8K2.t4249 = [0, 0, 94351752822, 347939339829, 346773435734, 89418559783, 2269197784, 0] := by
  decide +kernel

theorem rows4250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4250 = true := by
  decide +kernel

theorem tot4250 : totK PD2M8K2 D2M8K2.t4250 = [0, 0, 169811607595, 441636626837, 274011662726, 30386183309, 0, 0] := by
  decide +kernel

theorem rows4251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4251 = true := by
  decide +kernel

theorem tot4251 : totK PD2M8K2 D2M8K2.t4251 = [0, 0, 145831941930, 447306290569, 273199645663, 19415107432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
