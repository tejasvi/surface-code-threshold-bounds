import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1772 = true := by
  decide +kernel

theorem tot1772 : totK PD2M8K2 D2M8K2.t1772 = [0, 0, 172013056357, 458194462337, 265793550952, 23309776226, 0, 0] := by
  decide +kernel

theorem rows1773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1773 = true := by
  decide +kernel

theorem tot1773 : totK PD2M8K2 D2M8K2.t1773 = [0, 0, 174286811591, 446193253404, 265157233955, 18898566518, 0, 0] := by
  decide +kernel

theorem rows1774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1774 = true := by
  decide +kernel

theorem tot1774 : totK PD2M8K2 D2M8K2.t1774 = [0, 0, 93773531552, 395996161433, 373189418204, 47892142660, 1249641317, 0] := by
  decide +kernel

theorem rows1775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1775 = true := by
  decide +kernel

theorem tot1775 : totK PD2M8K2 D2M8K2.t1775 = [0, 0, 0, 254766009790, 485102438542, 130084887240, 3633193399, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
