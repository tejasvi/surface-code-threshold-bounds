import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9416 = true := by
  decide +kernel

theorem tot9416 : totK PD2M8K2 D2M8K2.t9416 = [0, 122444337579, 417146304768, 306044955369, 31980730127, 1128973710, 0, 0] := by
  decide +kernel

theorem rows9417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9417 = true := by
  decide +kernel

theorem tot9417 : totK PD2M8K2 D2M8K2.t9417 = [0, 0, 228832021626, 486708309991, 153794174213, 8318278252, 0, 0] := by
  decide +kernel

theorem rows9418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9418 = true := by
  decide +kernel

theorem tot9418 : totK PD2M8K2 D2M8K2.t9418 = [0, 121082670842, 353159077557, 316861403983, 77850942537, 3462014130, 0, 0] := by
  decide +kernel

theorem rows9419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9419 = true := by
  decide +kernel

theorem tot9419 : totK PD2M8K2 D2M8K2.t9419 = [0, 171005201168, 440123471666, 273581665512, 29989770019, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
