import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1708 = true := by
  decide +kernel

theorem tot1708 : totK PD2M8K2 D2M8K2.t1708 = [0, 0, 197457842865, 473711326650, 204312655239, 25733911244, 6969953709, 0] := by
  decide +kernel

theorem rows1709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1709 = true := by
  decide +kernel

theorem tot1709 : totK PD2M8K2 D2M8K2.t1709 = [0, 0, 196768256022, 448287945532, 202254967967, 12409643806, 0, 0] := by
  decide +kernel

theorem rows1710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1710 = true := by
  decide +kernel

theorem tot1710 : totK PD2M8K2 D2M8K2.t1710 = [0, 0, 23302704816, 310215867285, 455722054033, 100320472648, 1369150432, 0] := by
  decide +kernel

theorem rows1711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1711 = true := by
  decide +kernel

theorem tot1711 : totK PD2M8K2 D2M8K2.t1711 = [0, 0, 73511032432, 360910413095, 405924154363, 51264310878, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
