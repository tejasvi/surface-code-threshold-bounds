import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4672 = true := by
  decide +kernel

theorem tot4672 : totK PD2M8K2 D2M8K2.t4672 = [0, 0, 190501155008, 471726867946, 210520360153, 12595094539, 0, 0] := by
  decide +kernel

theorem rows4673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4673 = true := by
  decide +kernel

theorem tot4673 : totK PD2M8K2 D2M8K2.t4673 = [0, 0, 173835668149, 490507844403, 209530123444, 6376447579, 0, 0] := by
  decide +kernel

theorem rows4674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4674 = true := by
  decide +kernel

theorem tot4674 : totK PD2M8K2 D2M8K2.t4674 = [0, 0, 191738912984, 473769069311, 207982272403, 12403393969, 0, 0] := by
  decide +kernel

theorem rows4675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4675 = true := by
  decide +kernel

theorem tot4675 : totK PD2M8K2 D2M8K2.t4675 = [0, 0, 167057596297, 473611320359, 241012878798, 12280293419, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
