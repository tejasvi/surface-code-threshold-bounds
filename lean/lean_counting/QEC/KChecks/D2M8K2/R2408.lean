import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9632 = true := by
  decide +kernel

theorem tot9632 : totK PD2M8K2 D2M8K2.t9632 = [0, 0, 198623495788, 461840649104, 213233031680, 17014456371, 0, 0] := by
  decide +kernel

theorem rows9633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9633 = true := by
  decide +kernel

theorem tot9633 : totK PD2M8K2 D2M8K2.t9633 = [0, 0, 171302389518, 485261980120, 205911345837, 6529097454, 0, 0] := by
  decide +kernel

theorem rows9634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9634 = true := by
  decide +kernel

theorem tot9634 : totK PD2M8K2 D2M8K2.t9634 = [0, 0, 168849847679, 470980104004, 210842654383, 10250051428, 0, 0] := by
  decide +kernel

theorem rows9635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9635 = true := by
  decide +kernel

theorem tot9635 : totK PD2M8K2 D2M8K2.t9635 = [0, 0, 0, 284192700537, 463405446768, 92145026188, 1369150432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
