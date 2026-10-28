import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5504 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5504 = true := by
  decide +kernel

theorem tot5504 : totK PA10K2 A10K2.t5504 = [0, 0, 527827404291, 1788009555982, 1835592129853, 528456027627, 32384659689, 0, 0, 0] := by
  decide +kernel

theorem rows5505 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5505 = true := by
  decide +kernel

theorem tot5505 : totK PA10K2 A10K2.t5505 = [0, 0, 308174862979, 1522169633350, 2078884396553, 756547437529, 59494161816, 0, 0, 0] := by
  decide +kernel

theorem rows5506 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5506 = true := by
  decide +kernel

theorem tot5506 : totK PA10K2 A10K2.t5506 = [0, 0, 0, 701723694659, 2142565994555, 1523788995613, 262515286030, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5507 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5507 = true := by
  decide +kernel

theorem tot5507 : totK PA10K2 A10K2.t5507 = [0, 0, 0, 495024608414, 1793335898337, 1819189203107, 478735809125, 31193351345, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
