import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11760 = true := by
  decide +kernel

theorem tot11760 : totK PD2M8K2 D2M8K2.t11760 = [0, 170242728511, 451734303111, 278891114584, 29350723805, 0, 0, 0] := by
  decide +kernel

theorem rows11761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11761 = true := by
  decide +kernel

theorem tot11761 : totK PD2M8K2 D2M8K2.t11761 = [0, 192383337098, 483441013765, 221097508041, 9424143550, 0, 0, 0] := by
  decide +kernel

theorem rows11762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11762 = true := by
  decide +kernel

theorem tot11762 : totK PD2M8K2 D2M8K2.t11762 = [0, 36931127369, 278736477025, 399282343564, 177081176423, 21400436502, 0, 0] := by
  decide +kernel

theorem rows11763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11763 = true := by
  decide +kernel

theorem tot11763 : totK PD2M8K2 D2M8K2.t11763 = [0, 0, 204213066416, 482811440175, 202362381956, 7928356585, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
