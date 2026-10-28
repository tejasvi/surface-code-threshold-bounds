import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9828 = true := by
  decide +kernel

theorem tot9828 : totK PD2M8K2 D2M8K2.t9828 = [0, 0, 167374097261, 474156472635, 245856127853, 8621296721, 0, 0] := by
  decide +kernel

theorem rows9829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9829 = true := by
  decide +kernel

theorem tot9829 : totK PD2M8K2 D2M8K2.t9829 = [0, 190297476963, 470008569521, 241869205433, 21445614977, 0, 0, 0] := by
  decide +kernel

theorem rows9830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9830 = true := by
  decide +kernel

theorem tot9830 : totK PD2M8K2 D2M8K2.t9830 = [0, 194171362263, 478674209256, 227391705708, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows9831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9831 = true := by
  decide +kernel

theorem tot9831 : totK PD2M8K2 D2M8K2.t9831 = [0, 52318161032, 326838880504, 429800923112, 92631882683, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
