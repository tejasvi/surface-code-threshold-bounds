import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3256 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3256 = true := by
  decide +kernel

theorem tot3256 : totK PA10K2 A10K2.t3256 = [0, 268341569713, 1469532234922, 2165206822715, 788425100742, 58055984352, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3257 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3257 = true := by
  decide +kernel

theorem tot3257 : totK PA10K2 A10K2.t3257 = [0, 241745644269, 1150381222302, 1937699740181, 1133784520856, 182537356348, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows3258 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3258 = true := by
  decide +kernel

theorem tot3258 : totK PA10K2 A10K2.t3258 = [0, 497071727381, 1839856509287, 1902746529397, 528783582361, 31939474209, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3259 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3259 = true := by
  decide +kernel

theorem tot3259 : totK PA10K2 A10K2.t3259 = [0, 0, 735857978566, 2280213232952, 1477943188109, 170891601188, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
