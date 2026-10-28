import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12032 = true := by
  decide +kernel

theorem tot12032 : totK PD2M8K2 D2M8K2.t12032 = [0, 149221269572, 457781609368, 289541475723, 21329352675, 0, 0, 0] := by
  decide +kernel

theorem rows12033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12033 = true := by
  decide +kernel

theorem tot12033 : totK PD2M8K2 D2M8K2.t12033 = [0, 0, 227154879469, 474426710776, 155946341446, 4811815119, 0, 0] := by
  decide +kernel

theorem rows12034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12034 = true := by
  decide +kernel

theorem tot12034 : totK PD2M8K2 D2M8K2.t12034 = [0, 33130447393, 196617571405, 420671160824, 207508145989, 16939352947, 0, 0] := by
  decide +kernel

theorem rows12035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12035 = true := by
  decide +kernel

theorem tot12035 : totK PD2M8K2 D2M8K2.t12035 = [0, 191918556959, 485974070146, 203833065826, 9731855779, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
