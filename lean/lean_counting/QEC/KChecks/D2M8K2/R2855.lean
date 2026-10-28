import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11420 = true := by
  decide +kernel

theorem tot11420 : totK PD2M8K2 D2M8K2.t11420 = [0, 0, 175981483662, 463679205539, 243358076401, 12473173638, 0, 0] := by
  decide +kernel

theorem rows11421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11421 = true := by
  decide +kernel

theorem tot11421 : totK PD2M8K2 D2M8K2.t11421 = [0, 0, 84875750405, 404230762772, 363771055511, 37490358240, 0, 0] := by
  decide +kernel

theorem rows11422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11422 = true := by
  decide +kernel

theorem tot11422 : totK PD2M8K2 D2M8K2.t11422 = [0, 0, 0, 209353707351, 489514408907, 153757239579, 5126512042, 0] := by
  decide +kernel

theorem rows11423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11423 = true := by
  decide +kernel

theorem tot11423 : totK PD2M8K2 D2M8K2.t11423 = [0, 0, 188462997637, 441016302539, 244729222045, 28192512174, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
