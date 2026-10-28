import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7380 = true := by
  decide +kernel

theorem tot7380 : totK PD2M8K2 D2M8K2.t7380 = [0, 175063820980, 469052580049, 245509876693, 15017320542, 0, 0, 0] := by
  decide +kernel

theorem rows7381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7381 = true := by
  decide +kernel

theorem tot7381 : totK PD2M8K2 D2M8K2.t7381 = [0, 87753052624, 341430899031, 365873020214, 107863454951, 13132762340, 0, 0] := by
  decide +kernel

theorem rows7382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7382 = true := by
  decide +kernel

theorem tot7382 : totK PD2M8K2 D2M8K2.t7382 = [0, 0, 167206509248, 451787257685, 260453988988, 16253030987, 0, 0] := by
  decide +kernel

theorem rows7383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7383 = true := by
  decide +kernel

theorem tot7383 : totK PD2M8K2 D2M8K2.t7383 = [0, 36575289639, 216404341578, 440490799776, 195204106794, 8209296672, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
