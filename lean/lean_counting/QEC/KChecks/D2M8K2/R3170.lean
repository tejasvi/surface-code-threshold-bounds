import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12680 = true := by
  decide +kernel

theorem tot12680 : totK PD2M8K2 D2M8K2.t12680 = [0, 0, 55967812879, 250530626023, 389193495777, 160785435249, 11991925116, 0] := by
  decide +kernel

theorem rows12681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12681 = true := by
  decide +kernel

theorem tot12681 : totK PD2M8K2 D2M8K2.t12681 = [0, 0, 171942256002, 460025296540, 245503825301, 16673170060, 0, 0] := by
  decide +kernel

theorem rows12682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12682 = true := by
  decide +kernel

theorem tot12682 : totK PD2M8K2 D2M8K2.t12682 = [0, 0, 179009229301, 463294354027, 237156512907, 16959211542, 0, 0] := by
  decide +kernel

theorem rows12683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12683 = true := by
  decide +kernel

theorem tot12683 : totK PD2M8K2 D2M8K2.t12683 = [0, 0, 0, 299799349814, 495027531253, 84883877796, 1096505104, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
