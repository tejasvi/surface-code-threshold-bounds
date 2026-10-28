import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2976 = true := by
  decide +kernel

theorem tot2976 : totK PD2M8K2 D2M8K2.t2976 = [0, 153178919461, 434880698042, 278148992316, 21899966717, 0, 0, 0] := by
  decide +kernel

theorem rows2977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2977 = true := by
  decide +kernel

theorem tot2977 : totK PD2M8K2 D2M8K2.t2977 = [0, 89959375667, 348282725922, 362351786062, 71379120124, 1096505104, 0, 0] := by
  decide +kernel

theorem rows2978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2978 = true := by
  decide +kernel

theorem tot2978 : totK PD2M8K2 D2M8K2.t2978 = [0, 0, 288552229130, 504705233220, 92115017851, 1069412848, 0, 0] := by
  decide +kernel

theorem rows2979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2979 = true := by
  decide +kernel

theorem tot2979 : totK PD2M8K2 D2M8K2.t2979 = [0, 190579556311, 442742529602, 231911977440, 42684742908, 2751351395, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
