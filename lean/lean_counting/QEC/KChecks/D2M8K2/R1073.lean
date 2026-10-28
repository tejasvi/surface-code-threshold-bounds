import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4292 = true := by
  decide +kernel

theorem tot4292 : totK PD2M8K2 D2M8K2.t4292 = [0, 0, 0, 176190439536, 457482712504, 242454134620, 14135324137, 0] := by
  decide +kernel

theorem rows4293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4293 = true := by
  decide +kernel

theorem tot4293 : totK PD2M8K2 D2M8K2.t4293 = [0, 0, 0, 200030963746, 464290051974, 221676349768, 18543664296, 0] := by
  decide +kernel

theorem rows4294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4294 = true := by
  decide +kernel

theorem tot4294 : totK PD2M8K2 D2M8K2.t4294 = [0, 0, 0, 190034052562, 467971089372, 217155491541, 9472410349, 0] := by
  decide +kernel

theorem rows4295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4295 = true := by
  decide +kernel

theorem tot4295 : totK PD2M8K2 D2M8K2.t4295 = [0, 0, 0, 34616516901, 386680277841, 426803716079, 41324034611, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
