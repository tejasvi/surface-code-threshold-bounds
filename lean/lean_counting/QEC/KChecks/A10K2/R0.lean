import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows0 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t0 = true := by
  decide +kernel

theorem tot0 : totK PA10K2 A10K2.t0 = [583306429412, 1971958953925, 1855514058966, 446245860195, 25686058060, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1 = true := by
  decide +kernel

theorem tot1 : totK PA10K2 A10K2.t1 = [290724629903, 1426269631537, 2181349179110, 939172420508, 75658969261, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2 = true := by
  decide +kernel

theorem tot2 : totK PA10K2 A10K2.t2 = [0, 502783514639, 1833270538094, 1875734295501, 490517721420, 30831673886, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3 = true := by
  decide +kernel

theorem tot3 : totK PA10K2 A10K2.t3 = [441280817487, 1666102046377, 1919163296175, 734410815918, 69011696700, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
