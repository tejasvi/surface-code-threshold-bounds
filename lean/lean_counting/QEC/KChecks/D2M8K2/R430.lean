import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1720 = true := by
  decide +kernel

theorem tot1720 : totK PD2M8K2 D2M8K2.t1720 = [0, 0, 0, 308514678777, 481665404679, 82236451697, 1096505104, 0] := by
  decide +kernel

theorem rows1721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1721 = true := by
  decide +kernel

theorem tot1721 : totK PD2M8K2 D2M8K2.t1721 = [0, 0, 164123406694, 380046600640, 256480529968, 71978847275, 3820764243, 0] := by
  decide +kernel

theorem rows1722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1722 = true := by
  decide +kernel

theorem tot1722 : totK PD2M8K2 D2M8K2.t1722 = [0, 0, 156612626113, 456990744791, 268541271717, 17095130119, 0, 0] := by
  decide +kernel

theorem rows1723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1723 = true := by
  decide +kernel

theorem tot1723 : totK PD2M8K2 D2M8K2.t1723 = [0, 0, 91564971474, 355897960161, 368680130132, 77436353274, 1232398321, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
