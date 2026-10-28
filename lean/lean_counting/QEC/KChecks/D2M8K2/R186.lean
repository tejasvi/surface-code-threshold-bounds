import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t744 = true := by
  decide +kernel

theorem tot744 : totK PD2M8K2 D2M8K2.t744 = [0, 0, 285788657732, 502264889435, 91625722754, 1310285577, 0, 0] := by
  decide +kernel

theorem rows745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t745 = true := by
  decide +kernel

theorem tot745 : totK PD2M8K2 D2M8K2.t745 = [0, 91103721418, 385391090673, 382777109710, 42374128191, 0, 0, 0] := by
  decide +kernel

theorem rows746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t746 = true := by
  decide +kernel

theorem tot746 : totK PD2M8K2 D2M8K2.t746 = [0, 171993157772, 448806109031, 267669446545, 20750996487, 0, 0, 0] := by
  decide +kernel

theorem rows747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t747 = true := by
  decide +kernel

theorem tot747 : totK PD2M8K2 D2M8K2.t747 = [0, 206006902524, 474649181139, 214403138227, 14872527055, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
