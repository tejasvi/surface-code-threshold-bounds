import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13992 = true := by
  decide +kernel

theorem tot13992 : totK PD2M8K2 D2M8K2.t13992 = [0, 0, 0, 225070045585, 499794832999, 140806342702, 2437267027, 0] := by
  decide +kernel

theorem rows13993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13993 = true := by
  decide +kernel

theorem tot13993 : totK PD2M8K2 D2M8K2.t13993 = [0, 155087447104, 321783412617, 142208200026, 164647358068, 91712697100, 6701800220, 0] := by
  decide +kernel

theorem rows13994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13994 = true := by
  decide +kernel

theorem tot13994 : totK PD2M8K2 D2M8K2.t13994 = [0, 170310898757, 464598131305, 243555562314, 13546164754, 0, 0, 0] := by
  decide +kernel

theorem rows13995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13995 = true := by
  decide +kernel

theorem tot13995 : totK PD2M8K2 D2M8K2.t13995 = [0, 0, 287672947446, 496734674323, 92875677457, 1275377855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
