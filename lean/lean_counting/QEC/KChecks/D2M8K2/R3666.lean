import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14664 = true := by
  decide +kernel

theorem tot14664 : totK PD2M8K2 D2M8K2.t14664 = [0, 173066691409, 406999547024, 241030411317, 68585668612, 3884009855, 0, 0] := by
  decide +kernel

theorem rows14665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14665 = true := by
  decide +kernel

theorem tot14665 : totK PD2M8K2 D2M8K2.t14665 = [0, 171652524958, 445366426559, 275410769021, 21306898609, 0, 0, 0] := by
  decide +kernel

theorem rows14666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14666 = true := by
  decide +kernel

theorem tot14666 : totK PD2M8K2 D2M8K2.t14666 = [0, 78886334381, 340079856591, 386040656197, 87927543044, 1268739303, 0, 0] := by
  decide +kernel

theorem rows14667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14667 = true := by
  decide +kernel

theorem tot14667 : totK PD2M8K2 D2M8K2.t14667 = [0, 0, 226428436880, 494408671637, 157334870862, 4683989726, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
