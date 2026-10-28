import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4560 = true := by
  decide +kernel

theorem tot4560 : totK PD2M8K2 D2M8K2.t4560 = [0, 0, 171238590237, 450174594608, 274458298296, 28915968716, 0, 0] := by
  decide +kernel

theorem rows4561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4561 = true := by
  decide +kernel

theorem tot4561 : totK PD2M8K2 D2M8K2.t4561 = [0, 0, 84345551113, 419468997327, 378733353930, 48273136770, 0, 0] := by
  decide +kernel

theorem rows4562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4562 = true := by
  decide +kernel

theorem tot4562 : totK PD2M8K2 D2M8K2.t4562 = [0, 0, 15404020736, 218095029483, 487515285654, 156497943525, 5439011083, 0] := by
  decide +kernel

theorem rows4563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4563 = true := by
  decide +kernel

theorem tot4563 : totK PD2M8K2 D2M8K2.t4563 = [0, 0, 203707415804, 473368060516, 222221124292, 22044312900, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
