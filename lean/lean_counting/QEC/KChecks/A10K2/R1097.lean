import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4388 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4388 = true := by
  decide +kernel

theorem tot4388 : totK PA10K2 A10K2.t4388 = [0, 479837724954, 1631200885712, 1722182345182, 777793695738, 149349304059, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows4389 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4389 = true := by
  decide +kernel

theorem tot4389 : totK PA10K2 A10K2.t4389 = [0, 357062740456, 1610654147600, 2042656248400, 679041304845, 47950908699, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4390 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4390 = true := by
  decide +kernel

theorem tot4390 : totK PA10K2 A10K2.t4390 = [0, 0, 725270644250, 2232864876834, 1533732235669, 183863729460, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4391 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4391 = true := by
  decide +kernel

theorem tot4391 : totK PA10K2 A10K2.t4391 = [0, 0, 577891989922, 1895642569244, 1781602886097, 478281248986, 31987755669, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
