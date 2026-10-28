import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13652 = true := by
  decide +kernel

theorem tot13652 : totK PD2M8K2 D2M8K2.t13652 = [0, 222581813003, 485101100125, 176681217689, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows13653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13653 = true := by
  decide +kernel

theorem tot13653 : totK PD2M8K2 D2M8K2.t13653 = [0, 184016415418, 475224058481, 220470090540, 14707859566, 0, 0, 0] := by
  decide +kernel

theorem rows13654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13654 = true := by
  decide +kernel

theorem tot13654 : totK PD2M8K2 D2M8K2.t13654 = [0, 194884812232, 478353177277, 211791284909, 7984731767, 0, 0, 0] := by
  decide +kernel

theorem rows13655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13655 = true := by
  decide +kernel

theorem tot13655 : totK PD2M8K2 D2M8K2.t13655 = [0, 134149638299, 439630806879, 290371569894, 21620872140, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
