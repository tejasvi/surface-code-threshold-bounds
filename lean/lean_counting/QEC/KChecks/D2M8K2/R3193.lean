import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12772 = true := by
  decide +kernel

theorem tot12772 : totK PD2M8K2 D2M8K2.t12772 = [0, 191552640869, 463874983622, 246935173771, 23188875746, 0, 0, 0] := by
  decide +kernel

theorem rows12773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12773 = true := by
  decide +kernel

theorem tot12773 : totK PD2M8K2 D2M8K2.t12773 = [0, 145376688296, 454852152685, 280717022624, 19270354569, 0, 0, 0] := by
  decide +kernel

theorem rows12774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12774 = true := by
  decide +kernel

theorem tot12774 : totK PD2M8K2 D2M8K2.t12774 = [0, 0, 240052679250, 504566277628, 144552802273, 2304167554, 0, 0] := by
  decide +kernel

theorem rows12775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12775 = true := by
  decide +kernel

theorem tot12775 : totK PD2M8K2 D2M8K2.t12775 = [0, 0, 189255968953, 456209418055, 223487640446, 15928044983, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
