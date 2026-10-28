import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8652 = true := by
  decide +kernel

theorem tot8652 : totK PD2M8K2 D2M8K2.t8652 = [0, 178816854721, 430673538712, 281655966548, 34628788584, 0, 0, 0] := by
  decide +kernel

theorem rows8653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8653 = true := by
  decide +kernel

theorem tot8653 : totK PD2M8K2 D2M8K2.t8653 = [0, 158950608487, 475959778362, 253983633892, 13130200480, 0, 0, 0] := by
  decide +kernel

theorem rows8654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8654 = true := by
  decide +kernel

theorem tot8654 : totK PD2M8K2 D2M8K2.t8654 = [0, 200852618732, 465632642931, 240122698430, 16214580071, 0, 0, 0] := by
  decide +kernel

theorem rows8655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8655 = true := by
  decide +kernel

theorem tot8655 : totK PD2M8K2 D2M8K2.t8655 = [0, 167394259733, 431698164126, 269123341518, 27860886373, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
