import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7748 = true := by
  decide +kernel

theorem tot7748 : totK PD2M8K2 D2M8K2.t7748 = [0, 0, 174985890020, 464512357085, 238884314878, 14741517864, 0, 0] := by
  decide +kernel

theorem rows7749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7749 = true := by
  decide +kernel

theorem tot7749 : totK PD2M8K2 D2M8K2.t7749 = [0, 0, 0, 294270203278, 507237225442, 89826973034, 1096505104, 0] := by
  decide +kernel

theorem rows7750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7750 = true := by
  decide +kernel

theorem tot7750 : totK PD2M8K2 D2M8K2.t7750 = [0, 0, 0, 250984839104, 490565848858, 135485371646, 5253830308, 0] := by
  decide +kernel

theorem rows7751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7751 = true := by
  decide +kernel

theorem tot7751 : totK PD2M8K2 D2M8K2.t7751 = [0, 0, 0, 174810789579, 468557941270, 182178503428, 9464357663, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
