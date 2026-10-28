import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5176 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5176 = true := by
  decide +kernel

theorem tot5176 : totK PA10K2 A10K2.t5176 = [0, 0, 0, 0, 853200420211, 2233311999386, 1270681434265, 145497162429, 0, 0] := by
  decide +kernel

theorem rows5177 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5177 = true := by
  decide +kernel

theorem tot5177 : totK PA10K2 A10K2.t5177 = [0, 583306429412, 1750750291517, 1574898593243, 411133584879, 114053196799, 253400523953, 120117387750, 6354482628, 0] := by
  decide +kernel

theorem rows5178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5178 = true := by
  decide +kernel

theorem tot5178 : totK PA10K2 A10K2.t5178 = [0, 286677691149, 1530917297555, 2152664658173, 839930378683, 67021457256, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5179 = true := by
  decide +kernel

theorem tot5179 : totK PA10K2 A10K2.t5179 = [0, 0, 479388229063, 1834425023084, 1841461822034, 481101254328, 30831673886, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
