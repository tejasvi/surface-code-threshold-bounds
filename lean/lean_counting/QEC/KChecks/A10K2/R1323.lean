import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5292 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5292 = true := by
  decide +kernel

theorem tot5292 : totK PA10K2 A10K2.t5292 = [0, 0, 453707117931, 1753763363573, 1997185468971, 561482956934, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows5293 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5293 = true := by
  decide +kernel

theorem tot5293 : totK PA10K2 A10K2.t5293 = [0, 0, 166357572221, 1105793307068, 2020465080731, 1199014405733, 240442163608, 20070762815, 0, 0] := by
  decide +kernel

theorem rows5294 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5294 = true := by
  decide +kernel

theorem tot5294 : totK PA10K2 A10K2.t5294 = [0, 0, 112037851608, 742265311663, 1881484796186, 1607488642627, 323237669019, 10747604052, 0, 0] := by
  decide +kernel

theorem rows5295 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5295 = true := by
  decide +kernel

theorem tot5295 : totK PA10K2 A10K2.t5295 = [0, 0, 465889755366, 1730049530548, 1899085827488, 630615565005, 51464731716, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
