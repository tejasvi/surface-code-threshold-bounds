import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5304 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5304 = true := by
  decide +kernel

theorem tot5304 : totK PA10K2 A10K2.t5304 = [0, 0, 174514764450, 945231162344, 1985488910941, 1348698211285, 248488922356, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5305 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5305 = true := by
  decide +kernel

theorem tot5305 : totK PA10K2 A10K2.t5305 = [0, 0, 446656167670, 1770143192421, 1970523197159, 553861253890, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows5306 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5306 = true := by
  decide +kernel

theorem tot5306 : totK PA10K2 A10K2.t5306 = [0, 0, 140655879272, 1016792536816, 1969361243516, 1274335943192, 283674502103, 24614390653, 0, 0] := by
  decide +kernel

theorem rows5307 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5307 = true := by
  decide +kernel

theorem tot5307 : totK PA10K2 A10K2.t5307 = [0, 0, 276095678165, 1200291381272, 1911917177697, 1151833859102, 177287303861, 5460492893, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
