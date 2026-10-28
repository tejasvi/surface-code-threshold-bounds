import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8752 = true := by
  decide +kernel

theorem tot8752 : totK PD2M8K2 D2M8K2.t8752 = [0, 157075251805, 454823644966, 276679202897, 24266549076, 0, 0, 0] := by
  decide +kernel

theorem rows8753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8753 = true := by
  decide +kernel

theorem tot8753 : totK PD2M8K2 D2M8K2.t8753 = [0, 181257342552, 466881307464, 248702296351, 16430132962, 0, 0, 0] := by
  decide +kernel

theorem rows8754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8754 = true := by
  decide +kernel

theorem tot8754 : totK PD2M8K2 D2M8K2.t8754 = [0, 0, 254191675278, 504679252041, 129574568333, 1232609433, 0, 0] := by
  decide +kernel

theorem rows8755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8755 = true := by
  decide +kernel

theorem tot8755 : totK PD2M8K2 D2M8K2.t8755 = [0, 0, 180144277397, 473702786639, 217035925893, 8399863532, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
