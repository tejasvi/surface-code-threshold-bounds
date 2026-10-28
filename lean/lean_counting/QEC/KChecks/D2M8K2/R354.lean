import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1416 = true := by
  decide +kernel

theorem tot1416 : totK PD2M8K2 D2M8K2.t1416 = [0, 171790514059, 408625567834, 240709931844, 64917585009, 3720136285, 0, 0] := by
  decide +kernel

theorem rows1417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1417 = true := by
  decide +kernel

theorem tot1417 : totK PD2M8K2 D2M8K2.t1417 = [0, 164783095876, 445016052694, 273199251719, 21698076958, 0, 0, 0] := by
  decide +kernel

theorem rows1418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1418 = true := by
  decide +kernel

theorem tot1418 : totK PD2M8K2 D2M8K2.t1418 = [0, 89222919167, 340956548322, 379223171463, 89025727860, 1268739303, 0, 0] := by
  decide +kernel

theorem rows1419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1419 = true := by
  decide +kernel

theorem tot1419 : totK PD2M8K2 D2M8K2.t1419 = [0, 0, 227036387596, 487413188877, 162238181637, 4745018860, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
