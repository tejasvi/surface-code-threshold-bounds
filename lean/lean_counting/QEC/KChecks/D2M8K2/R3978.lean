import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15912 = true := by
  decide +kernel

theorem tot15912 : totK PD2M8K2 D2M8K2.t15912 = [0, 0, 185153170764, 468813806786, 226108627951, 13386570024, 0, 0] := by
  decide +kernel

theorem rows15913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15913 = true := by
  decide +kernel

theorem tot15913 : totK PD2M8K2 D2M8K2.t15913 = [0, 0, 62510775476, 359186592196, 376883131072, 62572728454, 1095107716, 0] := by
  decide +kernel

theorem rows15914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15914 = true := by
  decide +kernel

theorem tot15914 : totK PD2M8K2 D2M8K2.t15914 = [0, 47364138482, 59972140372, 251254522092, 407347486025, 99737464219, 3882006667, 0] := by
  decide +kernel

theorem rows15915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15915 = true := by
  decide +kernel

theorem tot15915 : totK PD2M8K2 D2M8K2.t15915 = [0, 203258211453, 482004623475, 200946024695, 8050594960, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
