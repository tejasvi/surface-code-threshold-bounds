import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2280 = true := by
  decide +kernel

theorem tot2280 : totK PD2M8K2 D2M8K2.t2280 = [0, 0, 200637937666, 464421541984, 190030439353, 12052611869, 0, 0] := by
  decide +kernel

theorem rows2281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2281 = true := by
  decide +kernel

theorem tot2281 : totK PD2M8K2 D2M8K2.t2281 = [0, 180616041277, 456290716242, 234436813516, 21996613793, 0, 0, 0] := by
  decide +kernel

theorem rows2282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2282 = true := by
  decide +kernel

theorem tot2282 : totK PD2M8K2 D2M8K2.t2282 = [0, 156464172225, 461008204178, 250723388550, 17219605378, 0, 0, 0] := by
  decide +kernel

theorem rows2283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2283 = true := by
  decide +kernel

theorem tot2283 : totK PD2M8K2 D2M8K2.t2283 = [0, 0, 281919601702, 507829064375, 95217332208, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
