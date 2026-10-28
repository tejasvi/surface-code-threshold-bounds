import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5428 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5428 = true := by
  decide +kernel

theorem tot5428 : totK PA10K2 A10K2.t5428 = [0, 0, 364887720258, 1644577185858, 1987231363368, 641274537176, 52537548050, 0, 0, 0] := by
  decide +kernel

theorem rows5429 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5429 = true := by
  decide +kernel

theorem tot5429 : totK PA10K2 A10K2.t5429 = [0, 0, 309417675788, 1244487892042, 1893822072060, 1111159034159, 174460545905, 5460492893, 0, 0] := by
  decide +kernel

theorem rows5430 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5430 = true := by
  decide +kernel

theorem tot5430 : totK PA10K2 A10K2.t5430 = [0, 0, 490459378854, 1877655250044, 2021530119051, 492759073945, 12244162943, 0, 0, 0] := by
  decide +kernel

theorem rows5431 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5431 = true := by
  decide +kernel

theorem tot5431 : totK PA10K2 A10K2.t5431 = [0, 0, 0, 659442869556, 2026258319014, 1727316942132, 401702514465, 25734533292, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
