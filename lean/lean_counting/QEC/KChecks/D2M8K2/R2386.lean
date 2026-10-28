import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9544 = true := by
  decide +kernel

theorem tot9544 : totK PD2M8K2 D2M8K2.t9544 = [202979450227, 483971458121, 224352024604, 12373561556, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9545 = true := by
  decide +kernel

theorem tot9545 : totK PD2M8K2 D2M8K2.t9545 = [54785896243, 283296506667, 374741009556, 176567463301, 21381705809, 0, 0, 0] := by
  decide +kernel

theorem rows9546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9546 = true := by
  decide +kernel

theorem tot9546 : totK PD2M8K2 D2M8K2.t9546 = [0, 203761872232, 485325385965, 204958682048, 7817859210, 0, 0, 0] := by
  decide +kernel

theorem rows9547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9547 = true := by
  decide +kernel

theorem tot9547 : totK PD2M8K2 D2M8K2.t9547 = [86101696324, 258018799983, 372470658883, 175189259479, 8209296672, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
