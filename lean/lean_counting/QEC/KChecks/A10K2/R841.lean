import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3364 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3364 = true := by
  decide +kernel

theorem tot3364 : totK PA10K2 A10K2.t3364 = [0, 0, 550461195332, 1791137190453, 1618415815726, 598773997736, 237699008279, 37674914273, 0, 0] := by
  decide +kernel

theorem rows3365 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3365 = true := by
  decide +kernel

theorem tot3365 : totK PA10K2 A10K2.t3365 = [0, 0, 296440474885, 1521555691065, 2231942975106, 892312357748, 75314396370, 0, 0, 0] := by
  decide +kernel

theorem rows3366 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3366 = true := by
  decide +kernel

theorem tot3366 : totK PA10K2 A10K2.t3366 = [0, 0, 0, 488746020212, 1829160938452, 1877176628580, 491552037465, 31306924438, 0, 0] := by
  decide +kernel

theorem rows3367 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3367 = true := by
  decide +kernel

theorem tot3367 : totK PA10K2 A10K2.t3367 = [0, 0, 476659998554, 1633786117286, 1932453041033, 802746564617, 85412424331, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
