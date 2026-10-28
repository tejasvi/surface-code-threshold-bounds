import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4464 = true := by
  decide +kernel

theorem tot4464 : totK PD2M8K2 D2M8K2.t4464 = [0, 0, 174976021207, 466786338603, 224579248876, 13144444366, 0, 0] := by
  decide +kernel

theorem rows4465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4465 = true := by
  decide +kernel

theorem tot4465 : totK PD2M8K2 D2M8K2.t4465 = [0, 0, 0, 313442964141, 459330010354, 75441900428, 1021600638, 0] := by
  decide +kernel

theorem rows4466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4466 = true := by
  decide +kernel

theorem tot4466 : totK PD2M8K2 D2M8K2.t4466 = [0, 0, 82732615011, 343772507608, 328788180451, 77397063712, 3552795014, 0] := by
  decide +kernel

theorem rows4467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4467 = true := by
  decide +kernel

theorem tot4467 : totK PD2M8K2 D2M8K2.t4467 = [0, 0, 177199642935, 454834736144, 263027946323, 25454134109, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
