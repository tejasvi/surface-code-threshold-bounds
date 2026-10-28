import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4392 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4392 = true := by
  decide +kernel

theorem tot4392 : totK PA10K2 A10K2.t4392 = [0, 0, 456420085552, 1799168485630, 2006157978236, 560866511228, 33304392454, 0, 0, 0] := by
  decide +kernel

theorem rows4393 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4393 = true := by
  decide +kernel

theorem tot4393 : totK PA10K2 A10K2.t4393 = [0, 0, 585563886633, 1979421833105, 1852056192829, 392477218966, 11881401544, 0, 0, 0] := by
  decide +kernel

theorem rows4394 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4394 = true := by
  decide +kernel

theorem tot4394 : totK PA10K2 A10K2.t4394 = [0, 0, 446737136078, 1674207704247, 1895482324368, 571870154366, 50267370225, 0, 0, 0] := by
  decide +kernel

theorem rows4395 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4395 = true := by
  decide +kernel

theorem tot4395 : totK PA10K2 A10K2.t4395 = [0, 0, 160368739085, 1390263367162, 2259041500261, 802877527557, 58503570348, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
