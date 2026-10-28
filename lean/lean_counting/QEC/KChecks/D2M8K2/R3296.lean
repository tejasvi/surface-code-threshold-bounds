import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13184 = true := by
  decide +kernel

theorem tot13184 : totK PD2M8K2 D2M8K2.t13184 = [0, 0, 177181412552, 461341739665, 237856785190, 18484640963, 0, 0] := by
  decide +kernel

theorem rows13185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13185 = true := by
  decide +kernel

theorem tot13185 : totK PD2M8K2 D2M8K2.t13185 = [0, 0, 189305663180, 462542580103, 220363881480, 16702988424, 0, 0] := by
  decide +kernel

theorem rows13186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13186 = true := by
  decide +kernel

theorem tot13186 : totK PD2M8K2 D2M8K2.t13186 = [0, 0, 66838547507, 348589805747, 375097374467, 72198816001, 1095107716, 0] := by
  decide +kernel

theorem rows13187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13187 = true := by
  decide +kernel

theorem tot13187 : totK PD2M8K2 D2M8K2.t13187 = [0, 7559944729, 3901843494, 272778490553, 466501710376, 120016332161, 3882006667, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
