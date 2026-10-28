import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t280 = true := by
  decide +kernel

theorem tot280 : totK PD2M8K2 D2M8K2.t280 = [0, 181341888804, 478501929965, 250082079952, 11344267307, 0, 0, 0] := by
  decide +kernel

theorem rows281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t281 = true := by
  decide +kernel

theorem tot281 : totK PD2M8K2 D2M8K2.t281 = [0, 0, 276936835941, 503748488560, 116770541768, 1249641317, 0, 0] := by
  decide +kernel

theorem rows282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t282 = true := by
  decide +kernel

theorem tot282 : totK PD2M8K2 D2M8K2.t282 = [0, 0, 179866084973, 486661986411, 203167767038, 8537527025, 0, 0] := by
  decide +kernel

theorem rows283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t283 = true := by
  decide +kernel

theorem tot283 : totK PD2M8K2 D2M8K2.t283 = [179984371288, 422118442081, 152558201174, 62223232379, 76808017813, 12110122745, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
