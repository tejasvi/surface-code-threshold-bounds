import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3756 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3756 = true := by
  decide +kernel

theorem tot3756 : totK PA10K2 A10K2.t3756 = [0, 0, 0, 517963410913, 1853256852078, 1851990394490, 433110718286, 31608797364, 0, 0] := by
  decide +kernel

theorem rows3757 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3757 = true := by
  decide +kernel

theorem tot3757 : totK PA10K2 A10K2.t3757 = [0, 0, 0, 142526967412, 1324836426799, 2265788019708, 785977456587, 58552203207, 0, 0] := by
  decide +kernel

theorem rows3758 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3758 = true := by
  decide +kernel

theorem tot3758 : totK PA10K2 A10K2.t3758 = [0, 0, 0, 473480110892, 1620700675880, 1826003342904, 808339522123, 141559855606, 5546304973, 0] := by
  decide +kernel

theorem rows3759 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3759 = true := by
  decide +kernel

theorem tot3759 : totK PA10K2 A10K2.t3759 = [0, 0, 536209087732, 1742738995046, 1865516253546, 679052541904, 65186433417, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
