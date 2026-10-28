import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2168 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2168 = true := by
  decide +kernel

theorem tot2168 : totK PA10K2 A10K2.t2168 = [0, 0, 497593185566, 1737612202861, 1800172972994, 485593111322, 31193230065, 0, 0, 0] := by
  decide +kernel

theorem rows2169 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2169 = true := by
  decide +kernel

theorem tot2169 : totK PA10K2 A10K2.t2169 = [0, 0, 432501254355, 1809941225039, 1901196114976, 499187650370, 31690778550, 0, 0, 0] := by
  decide +kernel

theorem rows2170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2170 = true := by
  decide +kernel

theorem tot2170 : totK PA10K2 A10K2.t2170 = [0, 0, 633960202354, 2059828390271, 1691170070451, 284412585377, 6354609102, 0, 0, 0] := by
  decide +kernel

theorem rows2171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2171 = true := by
  decide +kernel

theorem tot2171 : totK PA10K2 A10K2.t2171 = [0, 0, 543899032263, 1696148185815, 1693064289549, 536010306613, 50109395967, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
