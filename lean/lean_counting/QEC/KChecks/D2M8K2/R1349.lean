import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5396 = true := by
  decide +kernel

theorem tot5396 : totK PD2M8K2 D2M8K2.t5396 = [0, 0, 0, 199850003837, 510614521992, 192816116313, 5364914253, 0] := by
  decide +kernel

theorem rows5397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5397 = true := by
  decide +kernel

theorem tot5397 : totK PD2M8K2 D2M8K2.t5397 = [0, 0, 154156719226, 393671383605, 262630279088, 95779022165, 6804944647, 0] := by
  decide +kernel

theorem rows5398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5398 = true := by
  decide +kernel

theorem tot5398 : totK PD2M8K2 D2M8K2.t5398 = [0, 0, 205664324645, 474467709907, 207657437951, 14062416558, 0, 0] := by
  decide +kernel

theorem rows5399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5399 = true := by
  decide +kernel

theorem tot5399 : totK PD2M8K2 D2M8K2.t5399 = [0, 0, 52666304755, 344298582882, 433224034909, 75411562260, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
