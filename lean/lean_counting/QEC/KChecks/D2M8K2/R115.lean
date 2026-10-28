import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t460 = true := by
  decide +kernel

theorem tot460 : totK PD2M8K2 D2M8K2.t460 = [0, 172236189744, 462282607362, 245073067283, 15425667935, 0, 0, 0] := by
  decide +kernel

theorem rows461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t461 = true := by
  decide +kernel

theorem tot461 : totK PD2M8K2 D2M8K2.t461 = [0, 0, 234304590304, 511177383499, 144624600402, 3499003824, 0, 0] := by
  decide +kernel

theorem rows462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t462 = true := by
  decide +kernel

theorem tot462 : totK PD2M8K2 D2M8K2.t462 = [0, 69288392984, 275817546758, 386962278166, 133629157589, 9550723410, 0, 0] := by
  decide +kernel

theorem rows463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t463 = true := by
  decide +kernel

theorem tot463 : totK PD2M8K2 D2M8K2.t463 = [0, 187923476790, 483705531026, 216486485908, 9956742354, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
