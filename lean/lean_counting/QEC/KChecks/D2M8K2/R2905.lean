import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11620 = true := by
  decide +kernel

theorem tot11620 : totK PD2M8K2 D2M8K2.t11620 = [0, 128060521418, 442229440055, 317357609305, 33651427147, 0, 0, 0] := by
  decide +kernel

theorem rows11621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11621 = true := by
  decide +kernel

theorem tot11621 : totK PD2M8K2 D2M8K2.t11621 = [0, 0, 217333286935, 494733904902, 168524586478, 5218872685, 0, 0] := by
  decide +kernel

theorem rows11622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11622 = true := by
  decide +kernel

theorem tot11622 : totK PD2M8K2 D2M8K2.t11622 = [0, 156462043252, 435647200155, 285124519910, 34007560109, 0, 0, 0] := by
  decide +kernel

theorem rows11623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11623 = true := by
  decide +kernel

theorem tot11623 : totK PD2M8K2 D2M8K2.t11623 = [0, 194457730940, 458747362351, 227715898722, 16931500750, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
