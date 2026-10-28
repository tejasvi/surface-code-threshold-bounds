import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13840 = true := by
  decide +kernel

theorem tot13840 : totK PD2M8K2 D2M8K2.t13840 = [0, 182629719100, 466416847756, 263929538824, 26978907353, 0, 0, 0] := by
  decide +kernel

theorem rows13841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13841 = true := by
  decide +kernel

theorem tot13841 : totK PD2M8K2 D2M8K2.t13841 = [0, 182988257225, 466855677858, 227761660007, 14200844523, 0, 0, 0] := by
  decide +kernel

theorem rows13842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13842 = true := by
  decide +kernel

theorem tot13842 : totK PD2M8K2 D2M8K2.t13842 = [0, 189651952381, 470407067002, 223320191468, 12811311009, 0, 0, 0] := by
  decide +kernel

theorem rows13843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13843 = true := by
  decide +kernel

theorem tot13843 : totK PD2M8K2 D2M8K2.t13843 = [0, 171767595418, 456109272532, 264719788906, 23282239808, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
