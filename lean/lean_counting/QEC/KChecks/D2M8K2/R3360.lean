import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13440 = true := by
  decide +kernel

theorem tot13440 : totK PD2M8K2 D2M8K2.t13440 = [0, 0, 165299715247, 476213124611, 252425153336, 23336204314, 0, 0] := by
  decide +kernel

theorem rows13441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13441 = true := by
  decide +kernel

theorem tot13441 : totK PD2M8K2 D2M8K2.t13441 = [0, 0, 0, 211353889517, 473291431992, 192624016544, 13604428459, 0] := by
  decide +kernel

theorem rows13442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13442 = true := by
  decide +kernel

theorem tot13442 : totK PD2M8K2 D2M8K2.t13442 = [0, 0, 85714291646, 366545157534, 354943722154, 89137402006, 1409560813, 0] := by
  decide +kernel

theorem rows13443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13443 = true := by
  decide +kernel

theorem tot13443 : totK PD2M8K2 D2M8K2.t13443 = [0, 0, 181788776543, 448716585423, 271489933228, 23034579892, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
