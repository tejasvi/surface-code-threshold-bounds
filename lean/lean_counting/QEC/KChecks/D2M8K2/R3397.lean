import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13588 = true := by
  decide +kernel

theorem tot13588 : totK PD2M8K2 D2M8K2.t13588 = [92274514042, 344830141762, 378762848052, 83534804425, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows13589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13589 = true := by
  decide +kernel

theorem tot13589 : totK PD2M8K2 D2M8K2.t13589 = [0, 229927980182, 490557874011, 171356063147, 5809569923, 0, 0, 0] := by
  decide +kernel

theorem rows13590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13590 = true := by
  decide +kernel

theorem tot13590 : totK PD2M8K2 D2M8K2.t13590 = [0, 182352020271, 468340401015, 223054329615, 16333648467, 0, 0, 0] := by
  decide +kernel

theorem rows13591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13591 = true := by
  decide +kernel

theorem tot13591 : totK PD2M8K2 D2M8K2.t13591 = [0, 197718212992, 475075405713, 200446298300, 9713690252, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
