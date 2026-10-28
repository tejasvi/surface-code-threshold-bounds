import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16036 = true := by
  decide +kernel

theorem tot16036 : totK PD2M8K2 D2M8K2.t16036 = [0, 0, 180530429488, 455279042767, 243478920745, 15905254346, 0, 0] := by
  decide +kernel

theorem rows16037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16037 = true := by
  decide +kernel

theorem tot16037 : totK PD2M8K2 D2M8K2.t16037 = [0, 0, 0, 336697346942, 460486754382, 72830112913, 1096505104, 0] := by
  decide +kernel

theorem rows16038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16038 = true := by
  decide +kernel

theorem tot16038 : totK PD2M8K2 D2M8K2.t16038 = [0, 0, 89926844651, 333469266408, 365100675106, 95851506444, 3884009855, 0] := by
  decide +kernel

theorem rows16039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16039 = true := by
  decide +kernel

theorem tot16039 : totK PD2M8K2 D2M8K2.t16039 = [0, 0, 181934085014, 469191973953, 228631603790, 10830497886, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
