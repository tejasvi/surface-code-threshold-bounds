import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13684 = true := by
  decide +kernel

theorem tot13684 : totK PD2M8K2 D2M8K2.t13684 = [0, 184218250875, 445126127848, 229511157245, 17104814242, 0, 0, 0] := by
  decide +kernel

theorem rows13685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13685 = true := by
  decide +kernel

theorem tot13685 : totK PD2M8K2 D2M8K2.t13685 = [0, 55761343512, 343440940674, 405467416773, 68883088209, 1096505104, 0, 0] := by
  decide +kernel

theorem rows13686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13686 = true := by
  decide +kernel

theorem tot13686 : totK PD2M8K2 D2M8K2.t13686 = [0, 36720198771, 275837210882, 447235994354, 109339684156, 3838026431, 0, 0] := by
  decide +kernel

theorem rows13687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13687 = true := by
  decide +kernel

theorem tot13687 : totK PD2M8K2 D2M8K2.t13687 = [0, 201918430787, 473903115262, 224346266621, 13120936057, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
