import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5628 = true := by
  decide +kernel

theorem tot5628 : totK PD2M8K2 D2M8K2.t5628 = [0, 188101075478, 484833375129, 220929660815, 11051716772, 0, 0, 0] := by
  decide +kernel

theorem rows5629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5629 = true := by
  decide +kernel

theorem tot5629 : totK PD2M8K2 D2M8K2.t5629 = [0, 156062270197, 454924984571, 259712874483, 16126223677, 0, 0, 0] := by
  decide +kernel

theorem rows5630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5630 = true := by
  decide +kernel

theorem tot5630 : totK PD2M8K2 D2M8K2.t5630 = [0, 204267115152, 474228961238, 210419473271, 11066126582, 0, 0, 0] := by
  decide +kernel

theorem rows5631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5631 = true := by
  decide +kernel

theorem tot5631 : totK PD2M8K2 D2M8K2.t5631 = [0, 174213702505, 464148581690, 225646168645, 13597322258, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
