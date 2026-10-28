import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6064 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6064 = true := by
  decide +kernel

theorem tot6064 : totK PA10K2 A10K2.t6064 = [0, 389158204174, 1591227692003, 2077801006864, 863496478243, 68306498920, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6065 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6065 = true := by
  decide +kernel

theorem tot6065 : totK PA10K2 A10K2.t6065 = [0, 492611964355, 1837997190481, 2048211606021, 611533117016, 25177607156, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6066 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6066 = true := by
  decide +kernel

theorem tot6066 : totK PA10K2 A10K2.t6066 = [0, 0, 667355711726, 2115103389045, 1855229582674, 325842991000, 6066958478, 0, 0, 0] := by
  decide +kernel

theorem rows6067 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6067 = true := by
  decide +kernel

theorem tot6067 : totK PA10K2 A10K2.t6067 = [0, 207216491586, 795723178884, 1554666158819, 1670473631023, 630068231058, 55043167628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
