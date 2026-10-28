import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9952 = true := by
  decide +kernel

theorem tot9952 : totK PD2M8K2 D2M8K2.t9952 = [0, 0, 0, 224909840735, 498321377284, 163302046018, 5219851397, 0] := by
  decide +kernel

theorem rows9953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9953 = true := by
  decide +kernel

theorem tot9953 : totK PD2M8K2 D2M8K2.t9953 = [0, 0, 0, 256604325217, 492116554740, 139635172279, 5159820892, 0] := by
  decide +kernel

theorem rows9954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9954 = true := by
  decide +kernel

theorem tot9954 : totK PD2M8K2 D2M8K2.t9954 = [0, 0, 179157307792, 419868904668, 227984953489, 64645567279, 7717210273, 0] := by
  decide +kernel

theorem rows9955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9955 = true := by
  decide +kernel

theorem tot9955 : totK PD2M8K2 D2M8K2.t9955 = [0, 0, 178225138194, 452493290940, 219984288816, 9777738085, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
