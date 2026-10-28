import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8708 = true := by
  decide +kernel

theorem tot8708 : totK PD2M8K2 D2M8K2.t8708 = [0, 193507833975, 474153070137, 230018799121, 14853644569, 0, 0, 0] := by
  decide +kernel

theorem rows8709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8709 = true := by
  decide +kernel

theorem tot8709 : totK PD2M8K2 D2M8K2.t8709 = [0, 109275099140, 434121735252, 319725635743, 36651997987, 0, 0, 0] := by
  decide +kernel

theorem rows8710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8710 = true := by
  decide +kernel

theorem tot8710 : totK PD2M8K2 D2M8K2.t8710 = [0, 0, 176450457805, 447365195274, 260646364317, 25368447013, 0, 0] := by
  decide +kernel

theorem rows8711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8711 = true := by
  decide +kernel

theorem tot8711 : totK PD2M8K2 D2M8K2.t8711 = [0, 0, 177301476476, 492742380359, 215398612253, 5362199427, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
