import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2128 = true := by
  decide +kernel

theorem tot2128 : totK PD2M8K2 D2M8K2.t2128 = [0, 0, 83644455044, 339666760794, 360965664303, 84763374797, 1369150432, 0] := by
  decide +kernel

theorem rows2129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2129 = true := by
  decide +kernel

theorem tot2129 : totK PD2M8K2 D2M8K2.t2129 = [0, 0, 14689906303, 342765586891, 442221524836, 60638061104, 0, 0] := by
  decide +kernel

theorem rows2130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2130 = true := by
  decide +kernel

theorem tot2130 : totK PD2M8K2 D2M8K2.t2130 = [0, 0, 208797091395, 494223421592, 184063144338, 5463989431, 0, 0] := by
  decide +kernel

theorem rows2131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2131 = true := by
  decide +kernel

theorem tot2131 : totK PD2M8K2 D2M8K2.t2131 = [0, 0, 183470735276, 462333553787, 216593801092, 12243442891, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
