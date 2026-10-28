import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7664 = true := by
  decide +kernel

theorem tot7664 : totK PD2M8K2 D2M8K2.t7664 = [0, 0, 68458728822, 300492519432, 404686427676, 93895620231, 3820764243, 0] := by
  decide +kernel

theorem rows7665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7665 = true := by
  decide +kernel

theorem tot7665 : totK PD2M8K2 D2M8K2.t7665 = [0, 0, 171081962328, 468419222238, 256275221739, 18134077576, 0, 0] := by
  decide +kernel

theorem rows7666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7666 = true := by
  decide +kernel

theorem tot7666 : totK PD2M8K2 D2M8K2.t7666 = [0, 0, 168597656713, 471771764077, 248182335218, 15364511697, 0, 0] := by
  decide +kernel

theorem rows7667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7667 = true := by
  decide +kernel

theorem tot7667 : totK PD2M8K2 D2M8K2.t7667 = [0, 0, 0, 221183090860, 503166449843, 153852459567, 4967996017, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
