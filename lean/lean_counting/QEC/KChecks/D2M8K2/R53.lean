import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t212 = true := by
  decide +kernel

theorem tot212 : totK PD2M8K2 D2M8K2.t212 = [0, 51547316217, 326020452745, 434991421622, 101246672701, 2860976293, 0, 0] := by
  decide +kernel

theorem rows213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t213 = true := by
  decide +kernel

theorem tot213 : totK PD2M8K2 D2M8K2.t213 = [0, 86934566719, 316082069218, 378411697834, 107582460712, 2423372772, 0, 0] := by
  decide +kernel

theorem rows214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t214 = true := by
  decide +kernel

theorem tot214 : totK PD2M8K2 D2M8K2.t214 = [0, 177287100980, 460166226009, 260116749386, 21560881184, 0, 0, 0] := by
  decide +kernel

theorem rows215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t215 = true := by
  decide +kernel

theorem tot215 : totK PD2M8K2 D2M8K2.t215 = [0, 174560280625, 477126040550, 241116286579, 12480931912, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
