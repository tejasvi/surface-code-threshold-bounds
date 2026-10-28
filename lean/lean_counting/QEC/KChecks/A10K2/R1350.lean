import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5400 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5400 = true := by
  decide +kernel

theorem tot5400 : totK PA10K2 A10K2.t5400 = [0, 526444441311, 1902109910779, 1931986320464, 544441375519, 32780555804, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5401 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5401 = true := by
  decide +kernel

theorem tot5401 : totK PA10K2 A10K2.t5401 = [0, 118398086739, 993723811514, 2137350559237, 1415231388283, 290936144878, 20328650499, 0, 0, 0] := by
  decide +kernel

theorem rows5402 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5402 = true := by
  decide +kernel

theorem tot5402 : totK PA10K2 A10K2.t5402 = [0, 192005935598, 972557108811, 1935214306810, 1544548352200, 329800553927, 11418542001, 0, 0, 0] := by
  decide +kernel

theorem rows5403 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5403 = true := by
  decide +kernel

theorem tot5403 : totK PA10K2 A10K2.t5403 = [0, 561377630039, 1900769862159, 1953503863776, 564686263151, 38526822855, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
