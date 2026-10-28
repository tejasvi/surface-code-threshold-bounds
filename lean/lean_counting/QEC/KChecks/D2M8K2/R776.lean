import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3104 = true := by
  decide +kernel

theorem tot3104 : totK PD2M8K2 D2M8K2.t3104 = [137371426407, 449633616840, 289345378739, 19916385134, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3105 = true := by
  decide +kernel

theorem tot3105 : totK PD2M8K2 D2M8K2.t3105 = [0, 199656292145, 487477952764, 188971285127, 9668735432, 0, 0, 0] := by
  decide +kernel

theorem rows3106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3106 = true := by
  decide +kernel

theorem tot3106 : totK PD2M8K2 D2M8K2.t3106 = [85279739208, 305946473829, 377840517868, 110040091531, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows3107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3107 = true := by
  decide +kernel

theorem tot3107 : totK PD2M8K2 D2M8K2.t3107 = [145995395680, 432344919242, 283706095036, 27320335855, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
