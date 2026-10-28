import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10116 = true := by
  decide +kernel

theorem tot10116 : totK PD2M8K2 D2M8K2.t10116 = [0, 0, 63371571171, 343298146025, 395680269642, 82586475759, 1171084559, 0] := by
  decide +kernel

theorem rows10117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10117 = true := by
  decide +kernel

theorem tot10117 : totK PD2M8K2 D2M8K2.t10117 = [0, 0, 0, 195942847290, 464890565518, 183417084604, 10425178834, 0] := by
  decide +kernel

theorem rows10118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10118 = true := by
  decide +kernel

theorem tot10118 : totK PD2M8K2 D2M8K2.t10118 = [0, 0, 165404781481, 459984585322, 252819773226, 22202731849, 1509187004, 0] := by
  decide +kernel

theorem rows10119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10119 = true := by
  decide +kernel

theorem tot10119 : totK PD2M8K2 D2M8K2.t10119 = [0, 0, 171694250802, 467821759018, 245087000100, 15353161701, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
