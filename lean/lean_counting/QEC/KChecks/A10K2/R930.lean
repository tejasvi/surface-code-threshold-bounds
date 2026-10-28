import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3720 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3720 = true := by
  decide +kernel

theorem tot3720 : totK PA10K2 A10K2.t3720 = [0, 0, 457783257613, 1782233484890, 2037571043511, 641505283266, 34170906557, 0, 0, 0] := by
  decide +kernel

theorem rows3721 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3721 = true := by
  decide +kernel

theorem tot3721 : totK PA10K2 A10K2.t3721 = [0, 0, 0, 495112319263, 1836034436211, 1757181972556, 421798486946, 30818366867, 0, 0] := by
  decide +kernel

theorem rows3722 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3722 = true := by
  decide +kernel

theorem tot3722 : totK PA10K2 A10K2.t3722 = [0, 0, 481164232304, 1728817608293, 1886594939179, 626627410000, 42002851587, 0, 0, 0] := by
  decide +kernel

theorem rows3723 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3723 = true := by
  decide +kernel

theorem tot3723 : totK PA10K2 A10K2.t3723 = [0, 0, 296762186447, 1502427497159, 2123201014915, 780438887715, 58994932240, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
