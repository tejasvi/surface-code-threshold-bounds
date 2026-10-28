import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9960 = true := by
  decide +kernel

theorem tot9960 : totK PD2M8K2 D2M8K2.t9960 = [0, 0, 0, 303344945902, 498325886187, 89257027081, 1164319620, 0] := by
  decide +kernel

theorem rows9961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9961 = true := by
  decide +kernel

theorem tot9961 : totK PD2M8K2 D2M8K2.t9961 = [0, 0, 149090311686, 441061055205, 282349173471, 21448984392, 0, 0] := by
  decide +kernel

theorem rows9962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9962 = true := by
  decide +kernel

theorem tot9962 : totK PD2M8K2 D2M8K2.t9962 = [0, 0, 157954517026, 456532044714, 253884026853, 16285100441, 0, 0] := by
  decide +kernel

theorem rows9963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9963 = true := by
  decide +kernel

theorem tot9963 : totK PD2M8K2 D2M8K2.t9963 = [0, 0, 89904623429, 365830952029, 356057972089, 58444649871, 1096505104, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
