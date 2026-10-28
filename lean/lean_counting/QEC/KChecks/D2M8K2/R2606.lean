import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10424 = true := by
  decide +kernel

theorem tot10424 : totK PD2M8K2 D2M8K2.t10424 = [0, 0, 175901179002, 400865462048, 249826737924, 86329709301, 4239164426, 0] := by
  decide +kernel

theorem rows10425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10425 = true := by
  decide +kernel

theorem tot10425 : totK PD2M8K2 D2M8K2.t10425 = [0, 0, 180879612968, 454040242422, 260930805973, 20608918399, 0, 0] := by
  decide +kernel

theorem rows10426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10426 = true := by
  decide +kernel

theorem tot10426 : totK PD2M8K2 D2M8K2.t10426 = [0, 0, 88554027754, 382918665381, 362362234232, 59115049430, 1198073392, 0] := by
  decide +kernel

theorem rows10427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10427 = true := by
  decide +kernel

theorem tot10427 : totK PD2M8K2 D2M8K2.t10427 = [0, 0, 0, 237892839553, 492932371457, 165105550330, 8470662040, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
