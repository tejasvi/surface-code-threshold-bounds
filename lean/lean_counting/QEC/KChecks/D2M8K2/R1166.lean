import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4664 = true := by
  decide +kernel

theorem tot4664 : totK PD2M8K2 D2M8K2.t4664 = [0, 179036101606, 475492766242, 239913880922, 14089197607, 0, 0, 0] := by
  decide +kernel

theorem rows4665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4665 = true := by
  decide +kernel

theorem tot4665 : totK PD2M8K2 D2M8K2.t4665 = [0, 0, 284482129221, 503672758978, 110647344562, 1268739303, 0, 0] := by
  decide +kernel

theorem rows4666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4666 = true := by
  decide +kernel

theorem tot4666 : totK PD2M8K2 D2M8K2.t4666 = [0, 0, 196597057423, 476004109806, 201720518357, 12747075600, 0, 0] := by
  decide +kernel

theorem rows4667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4667 = true := by
  decide +kernel

theorem tot4667 : totK PD2M8K2 D2M8K2.t4667 = [0, 0, 220240700124, 509854689683, 163239871980, 2522384997, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
