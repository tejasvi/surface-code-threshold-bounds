import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2436 = true := by
  decide +kernel

theorem tot2436 : totK PD2M8K2 D2M8K2.t2436 = [94445126902, 207386645009, 113648632478, 106582134745, 244563288210, 140518796219, 13326740810, 0] := by
  decide +kernel

theorem rows2437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2437 = true := by
  decide +kernel

theorem tot2437 : totK PD2M8K2 D2M8K2.t2437 = [177746797152, 459810620139, 262968295236, 19921065880, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2438 = true := by
  decide +kernel

theorem tot2438 : totK PD2M8K2 D2M8K2.t2438 = [177742938662, 476630506669, 248421170773, 12419793312, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2439 = true := by
  decide +kernel

theorem tot2439 : totK PD2M8K2 D2M8K2.t2439 = [0, 190603713786, 460564916085, 244820389164, 24261412795, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
