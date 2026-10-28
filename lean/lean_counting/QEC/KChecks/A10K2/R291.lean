import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1164 = true := by
  decide +kernel

theorem tot1164 : totK PA10K2 A10K2.t1164 = [0, 198880611318, 1370353515289, 2161266724787, 845093707429, 60970094597, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1165 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1165 = true := by
  decide +kernel

theorem tot1165 : totK PA10K2 A10K2.t1165 = [0, 0, 623051039458, 2069863809501, 1675220599986, 291103673540, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows1166 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1166 = true := by
  decide +kernel

theorem tot1166 : totK PA10K2 A10K2.t1166 = [0, 0, 492975416778, 1824515919196, 1953170680021, 542803470276, 31987876949, 0, 0, 0] := by
  decide +kernel

theorem rows1167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1167 = true := by
  decide +kernel

theorem tot1167 : totK PA10K2 A10K2.t1167 = [0, 0, 463891337180, 1742208318674, 1922368605516, 512762009503, 18676709864, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
