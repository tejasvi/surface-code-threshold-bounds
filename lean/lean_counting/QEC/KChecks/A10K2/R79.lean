import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows316 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t316 = true := by
  decide +kernel

theorem tot316 : totK PA10K2 A10K2.t316 = [0, 0, 461347808201, 1805638651023, 1885541240516, 549889373341, 32616029439, 0, 0, 0] := by
  decide +kernel

theorem rows317 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t317 = true := by
  decide +kernel

theorem tot317 : totK PA10K2 A10K2.t317 = [0, 0, 601162357313, 2011437102665, 1764058418819, 343283280029, 11458962993, 0, 0, 0] := by
  decide +kernel

theorem rows318 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t318 = true := by
  decide +kernel

theorem tot318 : totK PA10K2 A10K2.t318 = [0, 0, 329076529001, 1618908883034, 2074716863306, 617589689971, 37819272392, 0, 0, 0] := by
  decide +kernel

theorem rows319 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t319 = true := by
  decide +kernel

theorem tot319 : totK PA10K2 A10K2.t319 = [0, 174706470648, 388968101341, 773027288019, 1809771703492, 1222247094987, 200425006996, 6121173289, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
