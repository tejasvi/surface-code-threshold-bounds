import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8644 = true := by
  decide +kernel

theorem tot8644 : totK PD2M8K2 D2M8K2.t8644 = [82465828918, 295484437618, 369921056685, 135571424708, 10860462960, 0, 0, 0] := by
  decide +kernel

theorem rows8645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8645 = true := by
  decide +kernel

theorem tot8645 : totK PD2M8K2 D2M8K2.t8645 = [176557328776, 453492813010, 262373404315, 24284846815, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8646 = true := by
  decide +kernel

theorem tot8646 : totK PD2M8K2 D2M8K2.t8646 = [181745577975, 473042925745, 245996175563, 16073828668, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8647 = true := by
  decide +kernel

theorem tot8647 : totK PD2M8K2 D2M8K2.t8647 = [0, 285494337114, 496621782524, 118063895804, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
