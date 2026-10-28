import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15124 = true := by
  decide +kernel

theorem tot15124 : totK PD2M8K2 D2M8K2.t15124 = [0, 0, 204105838372, 476662681405, 213989035635, 12825268392, 0, 0] := by
  decide +kernel

theorem rows15125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15125 = true := by
  decide +kernel

theorem tot15125 : totK PD2M8K2 D2M8K2.t15125 = [0, 0, 176735494913, 447895939718, 260159809842, 21455415392, 0, 0] := by
  decide +kernel

theorem rows15126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15126 = true := by
  decide +kernel

theorem tot15126 : totK PD2M8K2 D2M8K2.t15126 = [0, 0, 106808449551, 429100010361, 313089604137, 25415650466, 0, 0] := by
  decide +kernel

theorem rows15127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15127 = true := by
  decide +kernel

theorem tot15127 : totK PD2M8K2 D2M8K2.t15127 = [0, 0, 0, 251858543720, 475396613888, 144954526809, 5395128787, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
