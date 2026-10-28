import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1644 = true := by
  decide +kernel

theorem tot1644 : totK PD2M8K2 D2M8K2.t1644 = [0, 121836556003, 441514188239, 316322983053, 36531974274, 0, 0, 0] := by
  decide +kernel

theorem rows1645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1645 = true := by
  decide +kernel

theorem tot1645 : totK PD2M8K2 D2M8K2.t1645 = [0, 0, 181307153627, 481312722683, 222397904322, 8585356005, 0, 0] := by
  decide +kernel

theorem rows1646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1646 = true := by
  decide +kernel

theorem tot1646 : totK PD2M8K2 D2M8K2.t1646 = [0, 93449281537, 309593153583, 335664283385, 148580814676, 8340560233, 0, 0] := by
  decide +kernel

theorem rows1647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1647 = true := by
  decide +kernel

theorem tot1647 : totK PD2M8K2 D2M8K2.t1647 = [0, 169898555163, 435613380312, 267299840438, 28277726092, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
