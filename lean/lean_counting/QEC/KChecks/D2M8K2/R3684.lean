import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14736 = true := by
  decide +kernel

theorem tot14736 : totK PD2M8K2 D2M8K2.t14736 = [87773917060, 404417481639, 356385332218, 44814646150, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14737 = true := by
  decide +kernel

theorem tot14737 : totK PD2M8K2 D2M8K2.t14737 = [0, 217317017404, 485006624901, 174895718478, 8423393484, 0, 0, 0] := by
  decide +kernel

theorem rows14738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14738 = true := by
  decide +kernel

theorem tot14738 : totK PD2M8K2 D2M8K2.t14738 = [106242434665, 355867305027, 333835935047, 86173358331, 3462014130, 0, 0, 0] := by
  decide +kernel

theorem rows14739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14739 = true := by
  decide +kernel

theorem tot14739 : totK PD2M8K2 D2M8K2.t14739 = [179478227130, 444061209087, 253484432174, 27283297862, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
