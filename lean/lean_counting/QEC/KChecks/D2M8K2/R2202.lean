import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8808 = true := by
  decide +kernel

theorem tot8808 : totK PD2M8K2 D2M8K2.t8808 = [0, 145185430739, 356678566975, 293426000096, 115276417359, 6804944647, 0, 0] := by
  decide +kernel

theorem rows8809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8809 = true := by
  decide +kernel

theorem tot8809 : totK PD2M8K2 D2M8K2.t8809 = [0, 151371707952, 436086837431, 287079358524, 30213577679, 0, 0, 0] := by
  decide +kernel

theorem rows8810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8810 = true := by
  decide +kernel

theorem tot8810 : totK PD2M8K2 D2M8K2.t8810 = [0, 88824698027, 365822063114, 374053544041, 75124507500, 1129969115, 0, 0] := by
  decide +kernel

theorem rows8811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8811 = true := by
  decide +kernel

theorem tot8811 : totK PD2M8K2 D2M8K2.t8811 = [0, 0, 220626359029, 484037184752, 168564196998, 7938575017, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
