import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13884 = true := by
  decide +kernel

theorem tot13884 : totK PD2M8K2 D2M8K2.t13884 = [0, 24177818059, 283969261336, 444453336067, 101094937373, 3667207281, 0, 0] := by
  decide +kernel

theorem rows13885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13885 = true := by
  decide +kernel

theorem tot13885 : totK PD2M8K2 D2M8K2.t13885 = [0, 189663867906, 455916588775, 245353467984, 20872377286, 0, 0, 0] := by
  decide +kernel

theorem rows13886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13886 = true := by
  decide +kernel

theorem tot13886 : totK PD2M8K2 D2M8K2.t13886 = [0, 203676089569, 483586526927, 217017829473, 12349646172, 0, 0, 0] := by
  decide +kernel

theorem rows13887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13887 = true := by
  decide +kernel

theorem tot13887 : totK PD2M8K2 D2M8K2.t13887 = [159085141884, 329999902476, 282216831232, 140982556259, 13552632951, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
