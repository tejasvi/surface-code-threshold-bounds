import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5448 = true := by
  decide +kernel

theorem tot5448 : totK PD2M8K2 D2M8K2.t5448 = [0, 0, 47735427621, 230922228074, 424116092731, 184572592709, 8073768252, 0] := by
  decide +kernel

theorem rows5449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5449 = true := by
  decide +kernel

theorem tot5449 : totK PD2M8K2 D2M8K2.t5449 = [0, 0, 187298638348, 463736254391, 246618459129, 22743924844, 0, 0] := by
  decide +kernel

theorem rows5450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5450 = true := by
  decide +kernel

theorem tot5450 : totK PD2M8K2 D2M8K2.t5450 = [0, 0, 196755543613, 479248296649, 216743616577, 12423165040, 0, 0] := by
  decide +kernel

theorem rows5451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5451 = true := by
  decide +kernel

theorem tot5451 : totK PD2M8K2 D2M8K2.t5451 = [0, 0, 0, 301807028558, 488265635210, 99236024076, 1198073392, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
