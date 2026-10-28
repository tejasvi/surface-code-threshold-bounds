import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5216 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5216 = true := by
  decide +kernel

theorem tot5216 : totK PA10K2 A10K2.t5216 = [0, 0, 480382104490, 1785355438673, 2063552222898, 736702341335, 58080315988, 0, 0, 0] := by
  decide +kernel

theorem rows5217 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5217 = true := by
  decide +kernel

theorem tot5217 : totK PA10K2 A10K2.t5217 = [0, 0, 317063359641, 1484531722129, 2088076242841, 901071060063, 70443152043, 0, 0, 0] := by
  decide +kernel

theorem rows5218 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5218 = true := by
  decide +kernel

theorem tot5218 : totK PA10K2 A10K2.t5218 = [0, 0, 0, 578005091251, 2157277719606, 2008194805570, 340195590910, 6066958478, 0, 0] := by
  decide +kernel

theorem rows5219 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5219 = true := by
  decide +kernel

theorem tot5219 : totK PA10K2 A10K2.t5219 = [0, 0, 427178422353, 1387900558918, 1594578807658, 1059207119135, 424554615903, 33787274580, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
