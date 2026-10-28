import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9428 = true := by
  decide +kernel

theorem tot9428 : totK PD2M8K2 D2M8K2.t9428 = [0, 0, 138624978578, 453398353673, 243049638964, 18422398003, 0, 0] := by
  decide +kernel

theorem rows9429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9429 = true := by
  decide +kernel

theorem tot9429 : totK PD2M8K2 D2M8K2.t9429 = [0, 0, 19982170097, 322148730840, 420290539359, 72646077482, 1138244013, 0] := by
  decide +kernel

theorem rows9430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9430 = true := by
  decide +kernel

theorem tot9430 : totK PD2M8K2 D2M8K2.t9430 = [0, 0, 188285920264, 457467668071, 221251703080, 19759852146, 0, 0] := by
  decide +kernel

theorem rows9431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9431 = true := by
  decide +kernel

theorem tot9431 : totK PD2M8K2 D2M8K2.t9431 = [0, 0, 211434707081, 492107262966, 188102198155, 6769157880, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
