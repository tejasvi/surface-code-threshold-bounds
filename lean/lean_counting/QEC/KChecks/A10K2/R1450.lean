import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5800 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5800 = true := by
  decide +kernel

theorem tot5800 : totK PA10K2 A10K2.t5800 = [0, 0, 0, 741471329909, 2147222233727, 1594035403251, 368987056819, 25351274858, 0, 0] := by
  decide +kernel

theorem rows5801 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5801 = true := by
  decide +kernel

theorem tot5801 : totK PA10K2 A10K2.t5801 = [0, 0, 286131565344, 1230811039865, 1981894103801, 1205143520845, 202535783191, 5459593153, 0, 0] := by
  decide +kernel

theorem rows5802 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5802 = true := by
  decide +kernel

theorem tot5802 : totK PA10K2 A10K2.t5802 = [0, 0, 307060401758, 1501550825782, 2209318406605, 953454148409, 76896540718, 0, 0, 0] := by
  decide +kernel

theorem rows5803 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5803 = true := by
  decide +kernel

theorem tot5803 : totK PA10K2 A10K2.t5803 = [0, 0, 320561472736, 1292657092751, 1958300665464, 1301505179752, 248605120577, 6853348008, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
