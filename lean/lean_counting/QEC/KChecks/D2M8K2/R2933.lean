import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11732 = true := by
  decide +kernel

theorem tot11732 : totK PD2M8K2 D2M8K2.t11732 = [0, 160081200723, 452209627105, 259612129051, 18883739269, 0, 0, 0] := by
  decide +kernel

theorem rows11733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11733 = true := by
  decide +kernel

theorem tot11733 : totK PD2M8K2 D2M8K2.t11733 = [0, 0, 281282322984, 502867462996, 107094498575, 1369150432, 0, 0] := by
  decide +kernel

theorem rows11734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11734 = true := by
  decide +kernel

theorem tot11734 : totK PD2M8K2 D2M8K2.t11734 = [0, 142487098875, 431867268720, 300401250302, 30952027089, 0, 0, 0] := by
  decide +kernel

theorem rows11735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11735 = true := by
  decide +kernel

theorem tot11735 : totK PD2M8K2 D2M8K2.t11735 = [0, 183259848411, 438760423352, 255531541010, 23494672053, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
