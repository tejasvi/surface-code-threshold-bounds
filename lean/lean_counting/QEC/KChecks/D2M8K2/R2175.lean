import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8700 = true := by
  decide +kernel

theorem tot8700 : totK PD2M8K2 D2M8K2.t8700 = [0, 0, 173729213524, 458238888941, 252881148043, 21922323184, 0, 0] := by
  decide +kernel

theorem rows8701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8701 = true := by
  decide +kernel

theorem tot8701 : totK PD2M8K2 D2M8K2.t8701 = [0, 0, 175830485202, 457890106471, 235726070014, 13182661443, 0, 0] := by
  decide +kernel

theorem rows8702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8702 = true := by
  decide +kernel

theorem tot8702 : totK PD2M8K2 D2M8K2.t8702 = [0, 0, 0, 342049912581, 499384452125, 53849426189, 0, 0] := by
  decide +kernel

theorem rows8703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8703 = true := by
  decide +kernel

theorem tot8703 : totK PD2M8K2 D2M8K2.t8703 = [0, 0, 155935246015, 385340724420, 288998957409, 69499218807, 1392055030, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
