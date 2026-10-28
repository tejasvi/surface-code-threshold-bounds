import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5480 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5480 = true := by
  decide +kernel

theorem tot5480 : totK PA10K2 A10K2.t5480 = [0, 0, 448056785648, 1806108746890, 1908803133157, 519827070084, 31987755669, 0, 0, 0] := by
  decide +kernel

theorem rows5481 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5481 = true := by
  decide +kernel

theorem tot5481 : totK PA10K2 A10K2.t5481 = [0, 0, 500821982819, 1842841028510, 1907065372072, 515190100345, 33739454647, 0, 0, 0] := by
  decide +kernel

theorem rows5482 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5482 = true := by
  decide +kernel

theorem tot5482 : totK PA10K2 A10K2.t5482 = [0, 0, 464615971677, 1795793455452, 2019704779437, 546022821104, 18754734689, 0, 0, 0] := by
  decide +kernel

theorem rows5483 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5483 = true := by
  decide +kernel

theorem tot5483 : totK PA10K2 A10K2.t5483 = [0, 0, 526885770501, 1810370772135, 1798428146902, 492825126418, 44363554315, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
