import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8940 = true := by
  decide +kernel

theorem tot8940 : totK PD2M8K2 D2M8K2.t8940 = [0, 0, 306760542085, 470611657340, 78085226721, 1053411165, 0, 0] := by
  decide +kernel

theorem rows8941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8941 = true := by
  decide +kernel

theorem tot8941 : totK PD2M8K2 D2M8K2.t8941 = [0, 100253179405, 339674783024, 334426253151, 81889655200, 3667207281, 0, 0] := by
  decide +kernel

theorem rows8942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8942 = true := by
  decide +kernel

theorem tot8942 : totK PD2M8K2 D2M8K2.t8942 = [0, 176078639137, 450744113234, 255001815991, 23194172382, 0, 0, 0] := by
  decide +kernel

theorem rows8943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8943 = true := by
  decide +kernel

theorem tot8943 : totK PD2M8K2 D2M8K2.t8943 = [36508988125, 193247596078, 412794748840, 250876443795, 22079973395, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
