import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t712 = true := by
  decide +kernel

theorem tot712 : totK PD2M8K2 D2M8K2.t712 = [0, 174492066259, 439489014117, 263510169675, 29050474606, 0, 0, 0] := by
  decide +kernel

theorem rows713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t713 = true := by
  decide +kernel

theorem tot713 : totK PD2M8K2 D2M8K2.t713 = [0, 202997900030, 485716156105, 205811587125, 10179897161, 0, 0, 0] := by
  decide +kernel

theorem rows714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t714 = true := by
  decide +kernel

theorem tot714 : totK PD2M8K2 D2M8K2.t714 = [0, 162424367125, 461316196148, 254651999937, 16701087924, 0, 0, 0] := by
  decide +kernel

theorem rows715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t715 = true := by
  decide +kernel

theorem tot715 : totK PD2M8K2 D2M8K2.t715 = [0, 195400380254, 471157745500, 214852479116, 12370590376, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
