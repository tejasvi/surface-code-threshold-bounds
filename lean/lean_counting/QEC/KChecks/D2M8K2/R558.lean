import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2232 = true := by
  decide +kernel

theorem tot2232 : totK PD2M8K2 D2M8K2.t2232 = [0, 0, 81840717124, 308955350244, 374142533045, 94889722649, 3667207281, 0] := by
  decide +kernel

theorem rows2233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2233 = true := by
  decide +kernel

theorem tot2233 : totK PD2M8K2 D2M8K2.t2233 = [0, 0, 169071438777, 478201481673, 251132103647, 9688941905, 0, 0] := by
  decide +kernel

theorem rows2234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2234 = true := by
  decide +kernel

theorem tot2234 : totK PD2M8K2 D2M8K2.t2234 = [0, 122982710737, 346895421094, 308873065718, 122303935542, 9183461301, 0, 0] := by
  decide +kernel

theorem rows2235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2235 = true := by
  decide +kernel

theorem tot2235 : totK PD2M8K2 D2M8K2.t2235 = [0, 183305118110, 450913320224, 238930934333, 17115888737, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
