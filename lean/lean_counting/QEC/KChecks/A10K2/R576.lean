import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2304 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2304 = true := by
  decide +kernel

theorem tot2304 : totK PA10K2 A10K2.t2304 = [0, 0, 0, 433370387576, 1726946356773, 2003140772307, 669252246594, 55103251982, 0, 0] := by
  decide +kernel

theorem rows2305 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2305 = true := by
  decide +kernel

theorem tot2305 : totK PA10K2 A10K2.t2305 = [0, 0, 0, 540279289734, 1934949681117, 1852723746927, 414267011821, 12917769548, 0, 0] := by
  decide +kernel

theorem rows2306 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2306 = true := by
  decide +kernel

theorem tot2306 : totK PA10K2 A10K2.t2306 = [0, 0, 0, 0, 596379704156, 1969235578087, 1633843097540, 390759204182, 25565504801, 0] := by
  decide +kernel

theorem rows2307 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2307 = true := by
  decide +kernel

theorem tot2307 : totK PA10K2 A10K2.t2307 = [0, 0, 0, 435231104081, 1524022686325, 1644497228925, 822276544692, 160920964499, 5453062850, 0] := by
  decide +kernel

end QECKChecks.A10K2
