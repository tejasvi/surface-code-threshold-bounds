import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3356 = true := by
  decide +kernel

theorem tot3356 : totK PD2M8K2 D2M8K2.t3356 = [0, 0, 286805345334, 510741346110, 94175570390, 1310517177, 0, 0] := by
  decide +kernel

theorem rows3357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3357 = true := by
  decide +kernel

theorem tot3357 : totK PD2M8K2 D2M8K2.t3357 = [0, 176578327322, 445847745052, 267861106303, 29289407505, 0, 0, 0] := by
  decide +kernel

theorem rows3358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3358 = true := by
  decide +kernel

theorem tot3358 : totK PD2M8K2 D2M8K2.t3358 = [0, 195826227595, 480428750872, 229453158031, 12417015735, 0, 0, 0] := by
  decide +kernel

theorem rows3359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3359 = true := by
  decide +kernel

theorem tot3359 : totK PD2M8K2 D2M8K2.t3359 = [0, 47261040553, 299849593248, 413174958166, 150347581933, 9654694938, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
