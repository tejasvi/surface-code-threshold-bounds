import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4288 = true := by
  decide +kernel

theorem tot4288 : totK PD2M8K2 D2M8K2.t4288 = [0, 0, 0, 245283434295, 507318360071, 148545658152, 1284046538, 0] := by
  decide +kernel

theorem rows4289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4289 = true := by
  decide +kernel

theorem tot4289 : totK PD2M8K2 D2M8K2.t4289 = [0, 0, 0, 243729002585, 446240587972, 179211630568, 12370580691, 0] := by
  decide +kernel

theorem rows4290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4290 = true := by
  decide +kernel

theorem tot4290 : totK PD2M8K2 D2M8K2.t4290 = [0, 0, 0, 256926128340, 499103956718, 135809428926, 10469726998, 0] := by
  decide +kernel

theorem rows4291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4291 = true := by
  decide +kernel

theorem tot4291 : totK PD2M8K2 D2M8K2.t4291 = [0, 0, 0, 161376458244, 446837545265, 280145211176, 19967460746, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
