import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12708 = true := by
  decide +kernel

theorem tot12708 : totK PD2M8K2 D2M8K2.t12708 = [0, 0, 103649279775, 408921475898, 343284091749, 32903672897, 0, 0] := by
  decide +kernel

theorem rows12709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12709 = true := by
  decide +kernel

theorem tot12709 : totK PD2M8K2 D2M8K2.t12709 = [0, 0, 207597649064, 454169676760, 224289355708, 15645245184, 0, 0] := by
  decide +kernel

theorem rows12710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12710 = true := by
  decide +kernel

theorem tot12710 : totK PD2M8K2 D2M8K2.t12710 = [0, 0, 198893230053, 485629708002, 212482812982, 10528882417, 0, 0] := by
  decide +kernel

theorem rows12711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12711 = true := by
  decide +kernel

theorem tot12711 : totK PD2M8K2 D2M8K2.t12711 = [0, 0, 200777732055, 462271061926, 225412421575, 15812961001, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
