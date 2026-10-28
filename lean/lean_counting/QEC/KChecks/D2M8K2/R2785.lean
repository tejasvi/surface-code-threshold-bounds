import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11140 = true := by
  decide +kernel

theorem tot11140 : totK PD2M8K2 D2M8K2.t11140 = [0, 75954101155, 219806536308, 368530452587, 198685096938, 17192599809, 0, 0] := by
  decide +kernel

theorem rows11141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11141 = true := by
  decide +kernel

theorem tot11141 : totK PD2M8K2 D2M8K2.t11141 = [0, 173094823338, 478284382095, 234125113396, 11038245751, 0, 0, 0] := by
  decide +kernel

theorem rows11142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11142 = true := by
  decide +kernel

theorem tot11142 : totK PD2M8K2 D2M8K2.t11142 = [0, 168436381521, 444978528806, 238932184832, 15124186524, 0, 0, 0] := by
  decide +kernel

theorem rows11143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11143 = true := by
  decide +kernel

theorem tot11143 : totK PD2M8K2 D2M8K2.t11143 = [0, 0, 268257157160, 502491384502, 115414602017, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
